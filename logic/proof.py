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
                    proof, truth = Prover(self.assumptions, statement.statement).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(
                            self.conclusion, Equivalence.NotOfNot, statement.statement
                        )
                        return self.proof, True

                # Applying De'Morgen's Law
                match statement:
                    case CompositePropositionAND(first=first, second=second):
                        proof, truth = Prover(
                            self.assumptions, ~first | ~second
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                Equivalence.DeMorgensLaw,
                                ~first | ~second,
                            )
                            return self.proof, True
                    case CompositePropositionOR(first=first, second=second):
                        proof, truth = Prover(
                            self.assumptions, ~first & ~second
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                Equivalence.DeMorgensLaw,
                                ~first & ~second,
                            )
                            return self.proof, True

            case CompositePropositionOR(first=first, second=second):
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
                    proof, truth = Prover(self.assumptions, ~(first & second)).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(
                            self.conclusion, Equivalence.DeMorgensLaw, ~(first & second)
                        )
                        return self.proof, True

            case CompositePropositionAND(first=first, second=second):
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
                    proof, truth = Prover(self.assumptions, ~(first | second)).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(
                            self.conclusion, Equivalence.DeMorgensLaw, ~(first | second)
                        )
                        return self.proof, True

            case CompositePropositionBICONDITIONAL(
                assumption=assumption, conclusion=conclusion
            ):
                # Applying definition of Bi-Conditional
                #  (p <-> q) -> (p -> q) & (q -> p)
                proof_p_implies_q, truth_p_implies_q = Prover(
                    self.assumptions.remove(self.conclusion),
                    IMPLY(assumption, conclusion),
                ).prove()
                proof_q_implies_p, truth_q_implies_p = Prover(
                    self.assumptions.remove(self.conclusion),
                    IMPLY(conclusion, assumption),
                ).prove()
                if truth_p_implies_q and truth_q_implies_p:
                    self.proof.extend(proof_p_implies_q)
                    self.proof.extend(proof_q_implies_p)
                    self.proof.add_step(
                        self.conclusion,
                        Equivalence.DefinitionOfBiConditional,
                        IMPLY(assumption, conclusion),
                        IMPLY(conclusion, assumption),
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
                case CompositePropositionNOT(statement=statement):
                    # Applying NotOfNot i.e. ~(~x) <-> x
                    if isinstance(statement, CompositePropositionNOT):
                        if statement.statement != self.conclusion:
                            if statement.statement not in self.assumptions:
                                proof, truth = Prover(
                                    self.assumptions.add(statement.statement),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.add_step(
                                        self.conclusion, Equivalence.NotOfNot, i
                                    )
                                    self.proof.extend(proof)
                                    return self.proof, True
                        else:
                            self.proof.add_step(
                                self.conclusion, Equivalence.NotOfNot, i
                            )
                            return self.proof, True

                    # Applying De'Morgan's Law
                    match statement:
                        case CompositePropositionAND(first=first, second=second):
                            if (~first | ~second) != self.conclusion:
                                if (~first | ~second) not in self.assumptions:
                                    proof, truth = Prover(
                                        self.assumptions.add(~first | ~second),
                                        self.conclusion,
                                    ).prove()
                                    if truth:
                                        self.proof.add_step(
                                            self.conclusion, Equivalence.DeMorgensLaw, i
                                        )
                                        self.proof.extend(proof)
                                        return proof, True
                            else:
                                self.proof.add_step(
                                    self.conclusion, Equivalence.DeMorgensLaw, i
                                )
                                return self.proof, True

                        case CompositePropositionOR(first=first, second=second):
                            if ~first & ~second != self.conclusion:
                                if (~first & ~second) not in self.assumptions:
                                    proof, truth = Prover(
                                        self.assumptions.add(~first & ~second),
                                        self.conclusion,
                                    ).prove()
                                    if truth:
                                        self.proof.add_step(
                                            self.conclusion, Equivalence.DeMorgensLaw, i
                                        )
                                        self.proof.extend(proof)
                                        return self.proof, True
                            else:
                                self.proof.add_step(
                                    self.conclusion, Equivalence.DeMorgensLaw, i
                                )
                                return self.proof, True

                case CompositePropositionOR(first=first, second=second):
                    # Applying Resolution
                    if isinstance(self.conclusion, CompositePropositionOR):
                        if self.conclusion.first == first:
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                ~second | self.conclusion.second,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                ~second | self.conclusion.second,
                            )
                            return self.proof, True
                        if self.conclusion.second == second:
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                ~first | self.conclusion.first,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                ~first | self.conclusion.first,
                            )
                            return self.proof, True
                        if self.conclusion.first == second:
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                ~first | self.conclusion.second,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                ~first | self.conclusion.second,
                            )
                            return self.proof, True
                        if self.conclusion.second == first:
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                ~second | self.conclusion.first,
                            ).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.Resolution,
                                i,
                                ~second | self.conclusion.first,
                            )
                            return self.proof, True

                    # Applying Disjunctive Syllogism
                    if self.conclusion == first:
                        proof, truth = Prover(
                            self.assumptions.remove(i), ~second
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.DisjunctiveSyllogism,
                                i,
                                ~second,
                            )
                            return self.proof, True
                    if self.conclusion == second:
                        proof, truth = Prover(
                            self.assumptions.remove(i), ~first
                        ).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion,
                                RulesOfInference.DisjunctiveSyllogism,
                                i,
                                ~first,
                            )
                            return self.proof, True

                    # Applying De'Morgen's Law
                    if isinstance(first, CompositePropositionNOT) and isinstance(
                        second, CompositePropositionNOT
                    ):
                        if ~(first.statement & second.statement) != self.conclusion:
                            if not (
                                ~(first.statement & second.statement)
                                in self.assumptions
                            ):
                                proof, truth = Prover(
                                    self.assumptions.add(
                                        ~(first.statement & second.statement)
                                    ),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.add_step(
                                        self.conclusion, Equivalence.DeMorgensLaw, i
                                    )
                                    self.proof.extend(proof)
                                    return self.proof, True
                        else:
                            self.proof.add_step(
                                self.conclusion, Equivalence.DeMorgensLaw, i
                            )
                            return self.proof, True

                case CompositePropositionAND(first=first, second=second):
                    # Applying De'Morgen's Law
                    if isinstance(first, CompositePropositionNOT) and isinstance(
                        second, CompositePropositionNOT
                    ):
                        if ~(first.statement | second.statement) != self.conclusion:
                            if not (
                                ~(first.statement | second.statement)
                                in self.assumptions
                            ):
                                proof, truth = Prover(
                                    self.assumptions.add(
                                        ~(first.statement | second.statement)
                                    ),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.add_step(
                                        self.conclusion, Equivalence.DeMorgensLaw, i
                                    )
                                    self.proof.extend(proof)
                                    return self.proof, True
                        else:
                            self.proof.add_step(
                                self.conclusion, Equivalence.DeMorgensLaw, i
                            )
                            return self.proof, True

                    # Applying Simplification
                    if self.conclusion not in (first, second):
                        if (
                            first not in self.assumptions
                            or second not in self.assumptions
                        ):
                            proof, truth = Prover(
                                self.assumptions.add(first, second), self.conclusion
                            ).prove()
                            if truth:
                                self.proof.add_step(
                                    self.conclusion, RulesOfInference.Simplification, i
                                )
                                self.proof.extend(proof)
                                return self.proof, True
                    else:
                        self.proof.add_step(
                            self.conclusion, RulesOfInference.Simplification, i
                        )
                        return self.proof, True

                case CompositePropositionCONDITIONAL(
                    assumption=assumption, conclusion=conclusion
                ):
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
                            if self.conclusion != conclusion:
                                proof, truth = Prover(
                                    self.assumptions.remove(i).add(conclusion),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.extend(proof)
                                    return self.proof, True
                            else:
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
                                proof, truth = Prover(
                                    self.assumptions.remove(i).add(~assumption),
                                    self.conclusion,
                                ).prove()
                                if truth:
                                    self.proof.extend(proof)
                                    return self.proof, True
                            else:
                                return self.proof, True

                    # Applying Hypothetical Syllogism
                    if isinstance(self.conclusion, CompositePropositionCONDITIONAL):
                        if self.conclusion.conclusion == conclusion:
                            proof, truth = Prover(
                                self.assumptions.remove(i),
                                IMPLY(self.conclusion.assumption, assumption),
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
                                self.proof.add_step(
                                    self.conclusion,
                                    RulesOfInference.HypotheticalSyllogism,
                                    i,
                                    IMPLY(self.conclusion.assumption, assumption),
                                )
                                return self.proof, True

                case CompositePropositionBICONDITIONAL(
                    assumption=assumption, conclusion=conclusion
                ):
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

                    if (
                        IMPLY(assumption, conclusion) not in self.assumptions
                        or IMPLY(conclusion, assumption) not in self.assumptions
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
