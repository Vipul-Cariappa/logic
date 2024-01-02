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
    Predicate,
    CompositePredicateForAll,
    CompositePredicateThereExists,
    Statement,
)

from .utils import universal_instantiation, existential_instantiation

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
    UniversalInstantiation = "Universal Instantiation"
    UniversalGeneralization = "Universal Generalization"
    ExistentialInstantiation = "Existential Instantiation"
    ExistentialGeneralization = "Existential Generalization"

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

    def get(self, statement: Statement) -> Statement:
        """
        Returns the statement

        Args:
            statement (Statement): statement to find

        Raises:
            ValueError: if statement not found

        Returns:
            Statement: found statement
        """
        for i in self.assumptions:
            if i == statement:
                return i
        raise ValueError("Given statement not found un the assumptions")


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


class Environment:
    """Class used for the automated proving"""

    def __init__(
        self,
        assumptions: Sequence[Statement] | Assumption,
    ) -> None:
        """Constructs an Environment to work on

        Args:
            assumptions (Sequence[Statement] | Assumption): Assumptions to be used in
                this environment
        """
        if isinstance(assumptions, Assumption):
            self.assumptions = assumptions
        else:
            self.assumptions = Assumption(assumptions)

    def _prove_decomposed_conclusion(self, to_prove: Statement) -> tuple[Proof, bool]:
        my_proof = Proof()

        match to_prove:
            case CompositePredicateForAll():
                universal_instantiation_statement = universal_instantiation(to_prove)
                if universal_instantiation_statement in self.assumptions:
                    my_proof.add_step(
                        to_prove,
                        RulesOfInference.UniversalGeneralization,
                        self.assumptions.get(universal_instantiation_statement),
                    )
                    return my_proof, True

                proof, truth = prove(
                    self.assumptions, universal_instantiation_statement
                )
                if truth:
                    my_proof.extend(proof)
                    my_proof.add_step(
                        to_prove,
                        RulesOfInference.UniversalGeneralization,
                        universal_instantiation_statement,
                    )
                    return my_proof, True

            case CompositePredicateThereExists():
                existential_instantiation_statement = existential_instantiation(
                    to_prove
                )
                if existential_instantiation_statement in self.assumptions:
                    my_proof.add_step(
                        to_prove,
                        RulesOfInference.ExistentialGeneralization,
                        self.assumptions.get(existential_instantiation_statement),
                    )
                    return my_proof, True

                proof, truth = prove(
                    self.assumptions, existential_instantiation_statement
                )
                if truth:
                    my_proof.extend(proof)
                    my_proof.add_step(
                        to_prove,
                        RulesOfInference.ExistentialGeneralization,
                        existential_instantiation_statement,
                    )
                    return my_proof, True

                universal_instantiation_statement = universal_instantiation(to_prove)
                if universal_instantiation_statement in self.assumptions:
                    my_proof.add_step(
                        to_prove,
                        RulesOfInference.ExistentialGeneralization,
                        self.assumptions.get(universal_instantiation_statement),
                    )
                    return my_proof, True

                proof, truth = prove(
                    self.assumptions, universal_instantiation_statement
                )
                if truth:
                    my_proof.extend(proof)
                    my_proof.add_step(
                        to_prove,
                        RulesOfInference.ExistentialGeneralization,
                        universal_instantiation_statement,
                    )
                    return my_proof, True

            case CompositePropositionNOT(statement=statement):
                # Applying NotOfNot i.e. ~(~x) <-> x
                if isinstance(statement, CompositePropositionNOT):
                    sub_conclusion = statement.statement
                    proof, truth = prove(self.assumptions, sub_conclusion)
                    if truth:
                        my_proof.extend(proof)
                        my_proof.add_step(
                            to_prove, Equivalence.NotOfNot, sub_conclusion
                        )
                        return my_proof, True

                # Applying De'Morgen's Law
                match statement:
                    case CompositePropositionAND(first, second):
                        sub_conclusion = ~first | ~second
                        proof, truth = prove(self.assumptions, sub_conclusion)
                        if truth:
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                Equivalence.DeMorgensLaw,
                                sub_conclusion,
                            )
                            return my_proof, True
                    case CompositePropositionOR(first, second):
                        sub_conclusion = ~first & ~second
                        proof, truth = prove(self.assumptions, sub_conclusion)
                        if truth:
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                Equivalence.DeMorgensLaw,
                                sub_conclusion,
                            )
                            return my_proof, True

            case CompositePropositionOR(first, second):
                # Applying x | ~x <-> True
                if first == ~second or ~first == second:
                    return (
                        Proof(
                            [
                                (
                                    to_prove,
                                    Equivalence.Complement,
                                    (to_prove,),
                                )
                            ]
                        ),
                        True,
                    )

                # Applying Addition
                proof_first, truth_first = prove(self.assumptions, first)
                if truth_first:
                    my_proof.extend(proof_first)
                    my_proof.add_step(
                        to_prove, RulesOfInference.Addition, first, second
                    )
                    return my_proof, True
                proof_second, truth_second = prove(self.assumptions, second)
                if truth_second:
                    my_proof.extend(proof_second)
                    my_proof.add_step(
                        to_prove, RulesOfInference.Addition, second, first
                    )
                    return my_proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(
                    second, CompositePropositionNOT
                ):
                    sub_conclusion = ~(first & second)
                    proof, truth = prove(self.assumptions, sub_conclusion)
                    if truth:
                        my_proof.extend(proof)
                        my_proof.add_step(
                            to_prove, Equivalence.DeMorgensLaw, sub_conclusion
                        )
                        return my_proof, True

            case CompositePropositionAND(first, second):
                # Applying x & ~x <-> False
                if first == ~second or ~first == second:
                    return Proof(), False

                # Applying Conjunction
                proof_first, truth_first = prove(self.assumptions, first)
                proof_second, truth_second = prove(self.assumptions, second)
                if truth_first and truth_second:
                    my_proof.extend(proof_first)
                    my_proof.extend(proof_second)
                    my_proof.add_step(
                        to_prove, RulesOfInference.Conjunction, first, second
                    )
                    return my_proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(
                    second, CompositePropositionNOT
                ):
                    sub_conclusion = ~(first | second)
                    proof, truth = prove(self.assumptions, sub_conclusion)
                    if truth:
                        my_proof.extend(proof)
                        my_proof.add_step(
                            to_prove, Equivalence.DeMorgensLaw, sub_conclusion
                        )
                        return my_proof, True

            case CompositePropositionBICONDITIONAL(assumption, conclusion):
                # Applying definition of Bi-Conditional
                #  (p <-> q) -> (p -> q) & (q -> p)
                assumption_implies_conclusion = IMPLY(assumption, conclusion)
                conclusion_implies_assumption = IMPLY(conclusion, assumption)
                proof_p_implies_q, truth_p_implies_q = prove(
                    self.assumptions,
                    assumption_implies_conclusion,
                )
                proof_q_implies_p, truth_q_implies_p = prove(
                    self.assumptions,
                    conclusion_implies_assumption,
                )
                if truth_p_implies_q and truth_q_implies_p:
                    my_proof.extend(proof_p_implies_q)
                    my_proof.extend(proof_q_implies_p)
                    my_proof.add_step(
                        to_prove,
                        Equivalence.DefinitionOfBiConditional,
                        assumption_implies_conclusion,
                        conclusion_implies_assumption,
                    )
                    return my_proof, True

        return Proof(), False

    def prove(self, to_prove: Statement) -> tuple[Proof, bool]:
        """Tries to prove the given to_prove with the given assumptions

        Args:
            to_prove (Statement): Statement to prove
        Returns:
            tuple[Proof, bool]: Proof to prove the conclusion if conclusion is true
                otherwise an empty Proof, True if the conclusion was proved
                otherwise False
        """
        my_proof = Proof()

        if to_prove in self.assumptions:
            return my_proof, True

        for i in self.assumptions.with_proposition(to_prove):
            match i:
                case CompositePredicateForAll(_, predicate):
                    # Applying Universal Instantiation
                    if isinstance(predicate, Predicate) and isinstance(
                        to_prove, Predicate
                    ):
                        if to_prove == predicate(*to_prove.variables):
                            my_proof.add_step(
                                to_prove, RulesOfInference.UniversalInstantiation, i
                            )
                            return my_proof, True

                    universal_instantiation_statement = universal_instantiation(i)
                    if universal_instantiation_statement not in self.assumptions:
                        proof, truth = prove(
                            self.assumptions.add(universal_instantiation_statement),
                            to_prove,
                        )
                        if truth:
                            my_proof.add_step(
                                universal_instantiation_statement,
                                RulesOfInference.UniversalInstantiation,
                                i,
                            )
                            my_proof.extend(proof)
                            return my_proof, True

                    existential_instantiation_statement = existential_instantiation(i)
                    if existential_instantiation_statement not in self.assumptions:
                        proof, truth = prove(
                            self.assumptions.add(existential_instantiation_statement),
                            to_prove,
                        )
                        if truth:
                            my_proof.add_step(
                                existential_instantiation_statement,
                                RulesOfInference.ExistentialInstantiation,
                                i,
                            )
                            my_proof.extend(proof)
                            return my_proof, True

                    # TODO: Apply Demorgans Law

                case CompositePredicateThereExists(_, predicate):
                    # Applying Existential Instantiation
                    existential_instantiation_statement = existential_instantiation(i)
                    if existential_instantiation_statement not in self.assumptions:
                        proof, truth = prove(
                            self.assumptions.add(existential_instantiation_statement),
                            to_prove,
                        )
                        if truth:
                            my_proof.add_step(
                                existential_instantiation_statement,
                                RulesOfInference.ExistentialInstantiation,
                                i,
                            )
                            my_proof.extend(proof)
                            return my_proof, True

                    # TODO: Apply Demorgans Law

                case CompositePropositionNOT(statement):
                    # TODO: Apply Demorgans Law for Predicates

                    if isinstance(statement, CompositePropositionNOT):
                        # Applying NotOfNot i.e. ~(~x) <-> x
                        sub_conclusion = statement.statement

                        if sub_conclusion == to_prove:
                            # x is the thing we want to prove
                            my_proof.add_step(to_prove, Equivalence.NotOfNot, i)
                            return my_proof, True

                        if sub_conclusion not in self.assumptions:
                            # x is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = prove(
                                self.assumptions.add(sub_conclusion),
                                to_prove,
                            )
                            if truth:
                                my_proof.add_step(to_prove, Equivalence.NotOfNot, i)
                                my_proof.extend(proof)
                                return my_proof, True

                    match statement:
                        # Applying De'Morgan's Law
                        case CompositePropositionAND(first, second):
                            sub_conclusion = ~first | ~second

                            if sub_conclusion == to_prove:
                                # sub_conclusion is the thing we want to prove
                                my_proof.add_step(to_prove, Equivalence.DeMorgensLaw, i)
                                return my_proof, True

                            if sub_conclusion not in self.assumptions:
                                # sub_conclusion is not the thing we want to prove
                                # so add it to the list of assumptions and continue
                                proof, truth = prove(
                                    self.assumptions.add(sub_conclusion),
                                    to_prove,
                                )
                                if truth:
                                    my_proof.add_step(
                                        to_prove, Equivalence.DeMorgensLaw, i
                                    )
                                    my_proof.extend(proof)
                                    return proof, True

                        case CompositePropositionOR(first, second):
                            sub_conclusion = ~first & ~second

                            if sub_conclusion == to_prove:
                                # sub_conclusion is the thing we want to prove
                                my_proof.add_step(to_prove, Equivalence.DeMorgensLaw, i)
                                return my_proof, True

                            if sub_conclusion not in self.assumptions:
                                # sub_conclusion is not the thing we want to prove
                                # so add it to the list of assumptions and continue
                                proof, truth = prove(
                                    self.assumptions.add(sub_conclusion),
                                    to_prove,
                                )
                                if truth:
                                    my_proof.add_step(
                                        to_prove, Equivalence.DeMorgensLaw, i
                                    )
                                    my_proof.extend(proof)
                                    return my_proof, True

                case CompositePropositionOR(first, second):
                    if isinstance(to_prove, CompositePropositionOR):
                        # Applying Resolution
                        if to_prove.first == first:
                            sub_conclusion = ~second | to_prove.second
                            proof, truth = prove(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            )
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return my_proof, True

                        if to_prove.second == second:
                            sub_conclusion = ~first | to_prove.first
                            proof, truth = prove(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            )
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return my_proof, True

                        if to_prove.first == second:
                            sub_conclusion = ~first | to_prove.second
                            proof, truth = prove(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            )
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return my_proof, True

                        if to_prove.second == first:
                            sub_conclusion = ~second | to_prove.first
                            proof, truth = prove(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            )
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                RulesOfInference.Resolution,
                                i,
                                sub_conclusion,
                            )
                            return my_proof, True

                    # Applying Disjunctive Syllogism
                    if to_prove == first:
                        sub_conclusion = ~second
                        proof, truth = prove(self.assumptions.remove(i), sub_conclusion)
                        if truth:
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                RulesOfInference.DisjunctiveSyllogism,
                                i,
                                sub_conclusion,
                            )
                            return my_proof, True
                    if to_prove == second:
                        sub_conclusion = ~first
                        proof, truth = prove(self.assumptions.remove(i), sub_conclusion)
                        if truth:
                            my_proof.extend(proof)
                            my_proof.add_step(
                                to_prove,
                                RulesOfInference.DisjunctiveSyllogism,
                                i,
                                sub_conclusion,
                            )
                            return my_proof, True

                    if isinstance(first, CompositePropositionNOT) and isinstance(
                        second, CompositePropositionNOT
                    ):
                        # Applying De'Morgen's Law
                        sub_conclusion = ~(first.statement & second.statement)

                        if sub_conclusion == to_prove:
                            # sub_conclusion is the thing we want to prove
                            my_proof.add_step(to_prove, Equivalence.DeMorgensLaw, i)
                            return my_proof, True

                        if sub_conclusion not in self.assumptions:
                            # sub_conclusion is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = prove(
                                self.assumptions.add(sub_conclusion),
                                to_prove,
                            )
                            if truth:
                                my_proof.add_step(to_prove, Equivalence.DeMorgensLaw, i)
                                my_proof.extend(proof)
                                return my_proof, True

                case CompositePropositionAND(first, second):
                    if isinstance(first, CompositePropositionNOT) and isinstance(
                        second, CompositePropositionNOT
                    ):
                        # Applying De'Morgen's Law
                        sub_conclusion = ~(first.statement | second.statement)

                        if sub_conclusion == to_prove:
                            # sub_conclusion is the thing we want to prove
                            my_proof.add_step(to_prove, Equivalence.DeMorgensLaw, i)
                            return my_proof, True

                        if sub_conclusion not in self.assumptions:
                            # sub_conclusion is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = prove(
                                self.assumptions.add(sub_conclusion),
                                to_prove,
                            )
                            if truth:
                                my_proof.add_step(to_prove, Equivalence.DeMorgensLaw, i)
                                my_proof.extend(proof)
                                return my_proof, True

                    # Applying Simplification
                    if to_prove in (first, second):
                        # first or second is the thing we want to prove
                        my_proof.add_step(to_prove, RulesOfInference.Simplification, i)
                        return my_proof, True

                    if not (
                        (first in self.assumptions) and (second in self.assumptions)
                    ):
                        # first or second is not the thing we want to prove
                        # so add it to the list of assumptions and continue
                        proof, truth = prove(
                            self.assumptions.add(first, second), to_prove
                        )
                        if truth:
                            my_proof.add_step(first, RulesOfInference.Simplification, i)
                            my_proof.add_step(
                                second, RulesOfInference.Simplification, i
                            )
                            my_proof.extend(proof)
                            return my_proof, True

                case CompositePropositionCONDITIONAL(assumption, conclusion):
                    # Applying Modus Ponens
                    if (
                        conclusion not in self.assumptions
                        and to_prove != assumption
                        and to_prove != ~conclusion
                    ):
                        proof, truth = prove(self.assumptions.remove(i), assumption)
                        if truth:
                            my_proof.extend(proof)
                            my_proof.add_step(
                                conclusion, RulesOfInference.ModusPonens, i, assumption
                            )
                            if to_prove == conclusion:
                                # conclusion is the thing we want to prove
                                return my_proof, True

                            # conclusion is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = prove(
                                self.assumptions.remove(i).add(conclusion),
                                to_prove,
                            )
                            if truth:
                                my_proof.extend(proof)
                                return my_proof, True

                    # Applying Modus Tollens
                    if (
                        ~assumption not in self.assumptions
                        and to_prove != ~conclusion
                        and to_prove != assumption
                    ):
                        proof, truth = prove(self.assumptions.remove(i), ~conclusion)
                        if truth:
                            my_proof.extend(proof)
                            my_proof.add_step(
                                ~assumption,
                                RulesOfInference.ModusTollens,
                                i,
                                ~conclusion,
                            )
                            if to_prove == ~assumption:
                                # ~assumption is the thing we want to prove
                                return my_proof, True

                            # ~assumption is not the thing we want to prove
                            # so add it to the list of assumptions and continue
                            proof, truth = prove(
                                self.assumptions.remove(i).add(~assumption),
                                to_prove,
                            )
                            if truth:
                                my_proof.extend(proof)
                                return my_proof, True

                    # Applying Hypothetical Syllogism
                    if isinstance(to_prove, CompositePropositionCONDITIONAL):
                        if to_prove.conclusion == conclusion:
                            sub_conclusion = IMPLY(to_prove.assumption, assumption)

                            proof, truth = prove(
                                self.assumptions.remove(i),
                                sub_conclusion,
                            )
                            if truth:
                                my_proof.extend(proof)
                                my_proof.add_step(
                                    to_prove,
                                    RulesOfInference.HypotheticalSyllogism,
                                    i,
                                    sub_conclusion,
                                )
                                return my_proof, True

                case CompositePropositionBICONDITIONAL(assumption, conclusion):
                    # Applying definition of Bi-Conditional
                    #  (p <-> q) -> (p -> q) & (q -> p)
                    if (
                        IMPLY(assumption, conclusion) == to_prove
                        or IMPLY(conclusion, assumption) == to_prove
                    ):
                        my_proof.add_step(
                            to_prove, Equivalence.DefinitionOfBiConditional, i
                        )
                        return my_proof, True

                    if not (
                        IMPLY(assumption, conclusion) in self.assumptions
                        and IMPLY(conclusion, assumption) in self.assumptions
                    ):
                        proof, truth = prove(
                            self.assumptions.remove(i).add(
                                IMPLY(conclusion, assumption),
                                IMPLY(assumption, conclusion),
                            ),
                            to_prove,
                        )
                        if truth:
                            my_proof.add_step(
                                to_prove,
                                Equivalence.DefinitionOfBiConditional,
                                i,
                            )
                            my_proof.extend(proof)
                            return my_proof, True

        return self._prove_decomposed_conclusion(to_prove)

    def check(self, statement: Statement) -> bool:
        """Checks if the given statement is True in the given environment

        Args:
            statement (Statement): Statement to check the truth value of

        Returns:
            bool: True if it can be proved to be true, otherwise False
        """
        return self.prove(statement)[-1]


def prove(
    assumptions: Assumption | Sequence[Statement], conclusion: Statement
) -> tuple[Proof, bool]:
    """Tries to prove the given conclusion using the given assumptions

    Args:
        assumptions (Assumption | Sequence[Statement]): Assumptions to use
        conclusion (Statement): Conclusion to prove

    Returns:
        tuple[Proof, bool]: Proof, Is the conclusion true
    """
    return Environment(assumptions).prove(conclusion)
