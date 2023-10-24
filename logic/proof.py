"""All functions and classes related to construction of
proofs, assumptions and Prover to automated proving"""

from enum import Enum
from typing import Any, Generator, Iterator, Sequence, TypeAlias, Union

from .proposition import (
    IMPLY,
    CompositePropositionAND,
    CompositePropositionBICONDITIONAL,
    CompositePropositionCONDITIONAL,
    CompositePropositionNOT,
    CompositePropositionOR,
    Statement,
)

AssumptionT: TypeAlias = "Assumption"
ProofT: TypeAlias = "Proof"
ProofStrategy: TypeAlias = Union["Equivalence", "RulesOfInference"]


ProofEntryT = tuple[Statement, ProofStrategy, tuple[Statement, ...]]


class Equivalence(Enum):
    """Enum to represent all type of equivalences"""

    DefinitionOfBiConditional = "Definition Of Bi-Conditional"
    DeMorgensLaw = "De'Morgen's Law"
    NotOfNot = "Not Of Not"
    Complement = "Complement"

    def __str__(self) -> str:
        return self.value


class RulesOfInference(Enum):
    """Enum of all Rules Of Inference which can be used to construct proofs"""

    ModusPonens = "Modus Ponens"
    ModusTollens = "Modus Tollens"
    HypotheticalSyllogism = "Hypothetical Syllogism"
    DisjunctiveSyllogism = "Disjunctive Syllogism"
    Addition = "Addition"
    Simplification = "Simplification"
    Conjunction = "Conjunction"
    Resolution = "Resolution"

    def __str__(self) -> str:
        return self.value


class Assumption:
    """Class to hold and operate on all assumptions used in a proof"""

    def __init__(
        self, assumptions: Sequence[Statement] | set[Statement] | AssumptionT
    ) -> None:
        """Constructs Assumption

        Args:
            assumptions (Sequence[Statement] | set[Statement] | AssumptionT): Sequence
                or set of Statements
        """
        if isinstance(assumptions, Assumption):
            self.assumptions: set[Statement] = set(assumptions.assumptions)
        else:
            self.assumptions = set(assumptions)

    def __contains__(self, key: Any) -> bool:
        return key in self.assumptions

    def __str__(self) -> str:
        result = ""
        for i in self.assumptions:
            result += f"{str(i):>28}\n"
        return result

    def with_proposition(
        self, statement: Statement
    ) -> Generator[Statement, None, None]:
        """
        Returns a generator of all assumptions with contain at least one proposition
        from statement

        Args:
            statement (Statement): Proportions to look for

        Yields:
            Generator[Statement, None, None]: Assumptions that contain the given
                proposition
        """
        individual_propositions = statement.extract()
        for i in self.assumptions:
            yielded = False
            for j in individual_propositions:
                if j in i and not yielded:
                    yielded = True
                    yield i

            if not yielded and statement in i:
                yield i

    def remove(self, *statements: Statement) -> AssumptionT:
        """
        Constructs and returns new Assumption that does not contain any of the given
        statements. statements can be 1 or more Statement.

        Returns:
            Assumption: Returns newly constructed Assumption
        """
        return Assumption(self.assumptions - {*statements})

    def add(self, *statement: Statement) -> AssumptionT:
        """
        Constructs and returns new Assumption that with all of the given statements.
        statements can be 1 or more Statement.

        Returns:
            Assumption: Returns newly constructed Assumption
        """
        return Assumption(self.assumptions.union({*statement}))


class Proof:
    """Class to create, operate and verify on a proof"""

    def __init__(self, proof: list[ProofEntryT] | None = None) -> None:
        """Constructs Proof object

        Args:
            proof (list[tuple[Statement, ProofStrategy, *Statement]] | None, optional):
                List of triple tuple
                (Conclusion, Rule of Inference or Equivalence use, Assumptions used).
                Defaults to None.
        """
        self.proof: list[ProofEntryT] = proof if proof else []

    def add_step(
        self, conclusion: Statement, strategy: ProofStrategy, *statements: Statement
    ) -> None:
        """Adds a new step to the proof

        Args:
            conclusion (Statement): Conclusion that is derived in this step
            strategy (ProofStrategy): The Equivalence or Rule of Inference
                used in this step
            statements (Statement): 1 or more statements used in this step
        """
        self.proof.append((conclusion, strategy, (*statements,)))

    def extend(self, proof: ProofT) -> None:
        """extend this proof with another proof

        Args:
            proof (ProofT): Another proof to extend this proof with
        """
        self.proof.extend(proof.proof)

    def __iter__(self) -> Iterator[ProofEntryT]:
        return iter(self.proof)

    def __str__(self) -> str:
        result = ""
        for conclusion, rof, statements in self:
            statements_string = "{" + ", ".join(str(i) for i in statements) + "}"
            result += f"{str(conclusion):>28} {str(rof):>28} {statements_string:28}\n"
        return result


class Prover:
    """Class used for the automated proving"""

    def __init__(
        self,
        assumptions: Sequence[Statement] | Assumption,
        conclusion: Statement,
    ) -> None:
        """Constructs Prover class

        Args:
            assumptions (Sequence[Statement] | Assumption): Assumptions to be used in
                the proof
            conclusion (Statement): Conclusion that we want to prove
        """
        if isinstance(assumptions, Assumption):
            self.assumptions = assumptions
        else:
            self.assumptions = Assumption(assumptions)
        self.conclusion = conclusion
        self.proof = Proof()

    def _prove_decomposed_conclusion(self) -> tuple[Proof, bool]:
        match self.conclusion:
            case CompositePropositionNOT(statement=statement):
                # Applying NotOfNot i.e. ~(~x) <-> x
                if isinstance(statement, CompositePropositionNOT):
                    sub_conclusion = statement.statement
                    proof, truth = Prover(self.assumptions, sub_conclusion).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(
                            self.conclusion, Equivalence.NotOfNot, sub_conclusion
                        )
                        return self.proof, True

                # Applying De'Morgen's Law
                match statement:
                    case CompositePropositionAND(first, second):
                        sub_conclusion = ~first | ~second
                        proof, truth = Prover(self.assumptions, sub_conclusion).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                Equivalence.DeMorgensLaw,
                                sub_conclusion,
                            )
                            return self.proof, True
                    case CompositePropositionOR(first, second):
                        sub_conclusion = ~first & ~second
                        proof, truth = Prover(self.assumptions, sub_conclusion).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                Equivalence.DeMorgensLaw,
                                sub_conclusion,
                            )
                            return self.proof, True

            case CompositePropositionOR(first, second):
                # Applying x | ~x <-> True
                if first == ~second or ~first == second:
                    return (
                        Proof(
                            [
                                (
                                    self.conclusion,
                                    Equivalence.Complement,
                                    (self.conclusion,),
                                )
                            ]
                        ),
                        True,
                    )

                # Applying Addition
                proof_first, truth_first = Prover(
                    self.assumptions.remove(self.conclusion), first
                ).prove()
                if truth_first:
                    self.proof.extend(proof_first)
                    self.proof.add_step(
                        self.conclusion, RulesOfInference.Addition, first, second
                    )
                    return self.proof, True
                proof_second, truth_second = Prover(
                    self.assumptions.remove(self.conclusion), second
                ).prove()
                if truth_second:
                    self.proof.extend(proof_second)
                    self.proof.add_step(
                        self.conclusion, RulesOfInference.Addition, second, first
                    )
                    return self.proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(
                    second, CompositePropositionNOT
                ):
                    sub_conclusion = ~(first & second)
                    proof, truth = Prover(self.assumptions, sub_conclusion).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(
                            self.conclusion, Equivalence.DeMorgensLaw, sub_conclusion
                        )
                        return self.proof, True

            case CompositePropositionAND(first, second):
                # Applying x & ~x <-> False
                if first == ~second or ~first == second:
                    return Proof(), False

                # Applying Conjunction
                proof_first, truth_first = Prover(
                    self.assumptions.remove(self.conclusion), first
                ).prove()
                proof_second, truth_second = Prover(
                    self.assumptions.remove(self.conclusion), second
                ).prove()
                if truth_first and truth_second:
                    self.proof.extend(proof_first)
                    self.proof.extend(proof_second)
                    self.proof.add_step(
                        self.conclusion, RulesOfInference.Conjunction, first, second
                    )
                    return self.proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(
                    second, CompositePropositionNOT
                ):
                    sub_conclusion = ~(first | second)
                    proof, truth = Prover(self.assumptions, sub_conclusion).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(
                            self.conclusion, Equivalence.DeMorgensLaw, sub_conclusion
                        )
                        return self.proof, True

            case CompositePropositionBICONDITIONAL(assumption, conclusion):
                # Applying definition of Bi-Conditional
                #  (p <-> q) -> (p -> q) & (q -> p)
                assumption_implies_conclusion = IMPLY(assumption, conclusion)
                conclusion_implies_assumption = IMPLY(conclusion, assumption)
                proof_p_implies_q, truth_p_implies_q = Prover(
                    self.assumptions.remove(self.conclusion),
                    assumption_implies_conclusion,
                ).prove()
                proof_q_implies_p, truth_q_implies_p = Prover(
                    self.assumptions.remove(self.conclusion),
                    conclusion_implies_assumption,
                ).prove()
                if truth_p_implies_q and truth_q_implies_p:
                    self.proof.extend(proof_p_implies_q)
                    self.proof.extend(proof_q_implies_p)
                    self.proof.add_step(
                        self.conclusion,
                        Equivalence.DefinitionOfBiConditional,
                        assumption_implies_conclusion,
                        conclusion_implies_assumption,
                    )
                    return self.proof, True

        return Proof(), False

    def prove(self) -> tuple[Proof, bool]:
        """Tries to prove the given conclusion with the given assumptions

        Returns:
            tuple[Proof, bool]: Proof to prove the conclusion if conclusion is true
                otherwise an empty Proof, True if the conclusion was proved
                otherwise False
        """
        if self.conclusion in self.assumptions:
            return self.proof, True

        for i in self.assumptions.with_proposition(self.conclusion):
            match i:
                case CompositePropositionNOT(statement):
                    if isinstance(statement, CompositePropositionNOT):
                        # Applying NotOfNot i.e. ~(~x) <-> x
                        sub_conclusion = statement.statement

                        if sub_conclusion == self.conclusion:
                            # x is the thing we want to prove
                            self.proof.add_step(
                                self.conclusion, Equivalence.NotOfNot, i
                            )
                            return self.proof, True

                        if sub_conclusion not in self.assumptions:
                            # x is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = Prover(
                                self.assumptions.add(sub_conclusion),
                                self.conclusion,
                            ).prove()
                            if truth:
                                self.proof.add_step(
                                    self.conclusion, Equivalence.NotOfNot, i
                                )
                                self.proof.extend(proof)
                                return self.proof, True

                    match statement:
                        # Applying De'Morgan's Law
                        case CompositePropositionAND(first, second):
                            sub_conclusion = ~first | ~second

                            if sub_conclusion == self.conclusion:
                                # sub_conclusion is the thing we want to prove
                                self.proof.add_step(
                                    self.conclusion, Equivalence.DeMorgensLaw, i
                                )
                                return self.proof, True

                            if sub_conclusion not in self.assumptions:
                                # sub_conclusion is not the thing we want to prove
                                # so add it to the list of assumptions and continue
                                proof, truth = Prover(
                                    self.assumptions.add(sub_conclusion),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.add_step(
                                        self.conclusion, Equivalence.DeMorgensLaw, i
                                    )
                                    self.proof.extend(proof)
                                    return proof, True

                        case CompositePropositionOR(first, second):
                            sub_conclusion = ~first & ~second

                            if sub_conclusion == self.conclusion:
                                # sub_conclusion is the thing we want to prove
                                self.proof.add_step(
                                    self.conclusion, Equivalence.DeMorgensLaw, i
                                )
                                return self.proof, True

                            if sub_conclusion not in self.assumptions:
                                # sub_conclusion is not the thing we want to prove
                                # so add it to the list of assumptions and continue
                                proof, truth = Prover(
                                    self.assumptions.add(sub_conclusion),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.add_step(
                                        self.conclusion, Equivalence.DeMorgensLaw, i
                                    )
                                    self.proof.extend(proof)
                                    return self.proof, True

                case CompositePropositionOR(first, second):
                    if isinstance(self.conclusion, CompositePropositionOR):
                        # Applying Resolution
                        if self.conclusion.first == first:
                            sub_conclusion = ~second | self.conclusion.second
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return self.proof, True

                        if self.conclusion.second == second:
                            sub_conclusion = ~first | self.conclusion.first
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return self.proof, True

                        if self.conclusion.first == second:
                            sub_conclusion = ~first | self.conclusion.second
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return self.proof, True

                        if self.conclusion.second == first:
                            sub_conclusion = ~second | self.conclusion.first
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return self.proof, True

                    # Applying Disjunctive Syllogism
                    if self.conclusion == first:
                        sub_conclusion = ~second
                        proof, truth = Prover(
                            self.assumptions.remove(i), sub_conclusion
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.DisjunctiveSyllogism,
                                i,
                                sub_conclusion,
                            )
                            return self.proof, True
                    if self.conclusion == second:
                        sub_conclusion = ~first
                        proof, truth = Prover(
                            self.assumptions.remove(i), sub_conclusion
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.DisjunctiveSyllogism,
                                i,
                                sub_conclusion,
                            )
                            return self.proof, True

                    if isinstance(first, CompositePropositionNOT) and isinstance(
                        second, CompositePropositionNOT
                    ):
                        # Applying De'Morgen's Law
                        sub_conclusion = ~(first.statement & second.statement)

                        if sub_conclusion == self.conclusion:
                            # sub_conclusion is the thing we want to prove
                            self.proof.add_step(
                                self.conclusion, Equivalence.DeMorgensLaw, i
                            )
                            return self.proof, True

                        if sub_conclusion not in self.assumptions:
                            # sub_conclusion is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = Prover(
                                self.assumptions.add(sub_conclusion),
                                self.conclusion,
                            ).prove()
                            if truth:
                                self.proof.add_step(
                                    self.conclusion, Equivalence.DeMorgensLaw, i
                                )
                                self.proof.extend(proof)
                                return self.proof, True

                case CompositePropositionAND(first, second):
                    if isinstance(first, CompositePropositionNOT) and isinstance(
                        second, CompositePropositionNOT
                    ):
                        # Applying De'Morgen's Law
                        sub_conclusion = ~(first.statement | second.statement)

                        if sub_conclusion == self.conclusion:
                            # sub_conclusion is the thing we want to prove
                            self.proof.add_step(
                                self.conclusion, Equivalence.DeMorgensLaw, i
                            )
                            return self.proof, True

                        if sub_conclusion not in self.assumptions:
                            # sub_conclusion is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = Prover(
                                self.assumptions.add(sub_conclusion),
                                self.conclusion,
                            ).prove()
                            if truth:
                                self.proof.add_step(
                                    self.conclusion, Equivalence.DeMorgensLaw, i
                                )
                                self.proof.extend(proof)
                                return self.proof, True

                    # Applying Simplification
                    if self.conclusion in (first, second):
                        # first or second is the thing we want to prove
                        self.proof.add_step(
                            self.conclusion, RulesOfInference.Simplification, i
                        )
                        return self.proof, True

                    if not (
                        (first in self.assumptions) and (second in self.assumptions)
                    ):
                        # first or second is not the thing we want to prove
                        # so add it to the list of assumptions and continue
                        proof, truth = Prover(
                            self.assumptions.add(first, second), self.conclusion
                        ).prove()
                        if truth:
                            self.proof.add_step(
                                self.conclusion, RulesOfInference.Simplification, i
                            )
                            self.proof.extend(proof)
                            return self.proof, True

                case CompositePropositionCONDITIONAL(assumption, conclusion):
                    # Applying Modus Ponens
                    if (
                        conclusion not in self.assumptions
                        and self.conclusion != assumption
                        and self.conclusion != ~conclusion
                    ):
                        proof, truth = Prover(
                            self.assumptions.remove(i), assumption
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                conclusion, RulesOfInference.ModusPonens, i, assumption
                            )
                            if self.conclusion == conclusion:
                                # conclusion is the thing we want to prove
                                return self.proof, True

                            # conclusion is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = Prover(
                                self.assumptions.remove(i).add(conclusion),
                                self.conclusion,
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
                                return self.proof, True

                    # Applying Modus Tollens
                    if (
                        ~assumption not in self.assumptions
                        and self.conclusion != ~conclusion
                        and self.conclusion != assumption
                    ):
                        proof, truth = Prover(
                            self.assumptions.remove(i), ~conclusion
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                ~assumption,
                                RulesOfInference.ModusTollens,
                                i,
                                ~conclusion,
                            )
                            if self.conclusion != ~assumption:
                                # ~assumption is the thing we want to prove
                                return self.proof, True

                            # ~assumption is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = Prover(
                                self.assumptions.remove(i).add(~assumption),
                                self.conclusion,
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
                                return self.proof, True

                    # Applying Hypothetical Syllogism
                    if isinstance(self.conclusion, CompositePropositionCONDITIONAL):
                        if self.conclusion.conclusion == conclusion:
                            sub_conclusion = IMPLY(
                                self.conclusion.assumption, assumption
                            )

                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
                                self.proof.add_step(
                                    self.conclusion,
                                    RulesOfInference.HypotheticalSyllogism,
                                    i,
                                    sub_conclusion,
                                )
                                return self.proof, True

                case CompositePropositionBICONDITIONAL(assumption, conclusion):
                    # Applying definition of Bi-Conditional
                    #  (p <-> q) -> (p -> q) & (q -> p)
                    if (
                        IMPLY(assumption, conclusion) == self.conclusion
                        or IMPLY(conclusion, assumption) == self.conclusion
                    ):
                        self.proof.add_step(
                            self.conclusion, Equivalence.DefinitionOfBiConditional, i
                        )
                        return self.proof, True

                    if not (
                        IMPLY(assumption, conclusion) in self.assumptions
                        and IMPLY(conclusion, assumption) in self.assumptions
                    ):
                        proof, truth = Prover(
                            self.assumptions.remove(i).add(
                                IMPLY(conclusion, assumption),
                                IMPLY(assumption, conclusion),
                            ),
                            self.conclusion,
                        ).prove()
                        if truth:
                            self.proof.add_step(
                                self.conclusion,
                                Equivalence.DefinitionOfBiConditional,
                                i,
                            )
                            self.proof.extend(proof)
                            return self.proof, True

        return self._prove_decomposed_conclusion()
