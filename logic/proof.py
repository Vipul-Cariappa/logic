from typing import Sequence, Generator, Iterator, TypeAlias, Any
from .proposition import (
    Statement,
    CompositePropositionAND,
    CompositePropositionNOT,
    CompositePropositionOR,
    CompositePropositionBICONDITIONAL,
    CompositePropositionCONDITIONAL,
    IMPLY,
)

from enum import Enum

AssumptionT: TypeAlias = "Assumption"
ProofT: TypeAlias = "Proof"


class ProofStrategy(Enum):
    pass


ProofEntryT = tuple[Statement, ProofStrategy, tuple[Statement, ...]]


class Equivalence(ProofStrategy):
    DefinitionOfBiConditional = "Definition Of Bi-Conditional"
    DeMorgensLaw = "De'Morgen's Law"
    NotOfNot = "Not Of Not"
    Complement = "Complement"

    def __str__(self) -> str:
        return self.value


class RulesOfInference(ProofStrategy):
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
    def __init__(self, assumptions: Sequence[Statement] | AssumptionT) -> None:
        if isinstance(assumptions, Assumption):
            self.assumptions: set[Statement] = set(assumptions.assumptions)
        else:
            self.assumptions = set(assumptions)

    def __contains__(self, key: Any) -> bool:
        return key in self.assumptions

    def __str__(self) -> str:
        result = ""
        for i in self.assumptions:
            result += "{:>28}\n".format(str(i))
        return result

    def with_proposition(self, prop: Statement) -> Generator[Statement, None, None]:
        individual_propositions = prop.extract()
        for i in self.assumptions:
            yielded = False
            for j in individual_propositions:
                if j in i and not yielded:
                    yielded = True
                    yield i

            if not yielded and prop in i:
                yield i

    def get(self) -> list[Statement]:
        return list(self.assumptions)

    def remove(self, statement: Statement) -> AssumptionT:
        return Assumption(list(self.assumptions - {statement}))


class Proof:
    def __init__(self, proof: list[ProofEntryT] | None = None) -> None:
        self.proof: list[ProofEntryT] = proof if proof else []

    def add_step(self, conclusion: Statement, roi: ProofStrategy, *statement: Statement) -> None:
        self.proof.append((conclusion, roi, (*statement,)))

    def extend(self, proof: ProofT) -> None:
        self.proof.extend(proof.proof)

    def __iter__(self) -> Iterator[ProofEntryT]:
        return iter(self.proof)

    def __str__(self) -> str:
        result = ""
        for conclusion, rof, statements in self:
            result += "{:>28} {:>28} {:28}\n".format(
                str(conclusion), str(rof), "{" + ", ".join(str(i) for i in statements) + "}"
            )
        return result


class Prover:
    def __init__(
        self,
        assumptions: Sequence[Statement] | Assumption,
        conclusion: Statement,
    ) -> None:
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
                        self.proof.add_step(self.conclusion, Equivalence.NotOfNot, statement.statement)
                        return self.proof, True

                # Applying De'Morgen's Law
                match statement:
                    case CompositePropositionAND(first=first, second=second):
                        proof, truth = Prover(self.assumptions, ~first | ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, ~first | ~second)
                            return self.proof, True
                    case CompositePropositionOR(first=first, second=second):
                        proof, truth = Prover(self.assumptions, ~first & ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, ~first & ~second)
                            return self.proof, True

            case CompositePropositionOR(first=first, second=second):
                # Applying x | ~x <-> True
                if first == ~second or ~first == second:
                    return Proof([(self.conclusion, Equivalence.Complement, (self.conclusion,))]), True

                # Applying Addition
                proof_first, truth_first = Prover(self.assumptions.remove(self.conclusion), first).prove()
                if truth_first:
                    self.proof.extend(proof_first)
                    self.proof.add_step(self.conclusion, RulesOfInference.Addition, first, second)
                    return self.proof, True
                proof_second, truth_second = Prover(self.assumptions.remove(self.conclusion), second).prove()
                if truth_second:
                    self.proof.extend(proof_second)
                    self.proof.add_step(self.conclusion, RulesOfInference.Addition, second, first)
                    return self.proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                    proof, truth = Prover(self.assumptions, ~(first & second)).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, ~(first & second))
                        return self.proof, True

            case CompositePropositionAND(first=first, second=second):
                # Applying x & ~x <-> False
                if first == ~second or ~first == second:
                    return Proof(), False

                # Applying Conjunction
                proof_first, truth_first = Prover(self.assumptions.remove(self.conclusion), first).prove()
                proof_second, truth_second = Prover(self.assumptions.remove(self.conclusion), second).prove()
                if truth_first and truth_second:
                    self.proof.extend(proof_first)
                    self.proof.extend(proof_second)
                    self.proof.add_step(self.conclusion, RulesOfInference.Conjunction, first, second)
                    return self.proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                    proof, truth = Prover(self.assumptions, ~(first | second)).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, ~(first | second))
                        return self.proof, True

            case CompositePropositionBICONDITIONAL(assumption=assumption, conclusion=conclusion):
                # Applying definition of Bi-Conditional
                #  (p <-> q) -> (p -> q) & (q -> p)
                proof_p_implies_q, truth_p_implies_q = Prover(
                    self.assumptions.remove(self.conclusion), IMPLY(assumption, conclusion)
                ).prove()
                proof_q_implies_p, truth_q_implies_p = Prover(
                    self.assumptions.remove(self.conclusion), IMPLY(conclusion, assumption)
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
        if self.conclusion in self.assumptions:
            return self.proof, True

        for i in self.assumptions.with_proposition(self.conclusion):
            match i:
                case CompositePropositionNOT(statement=statement):
                    # Applying NotOfNot i.e. ~(~x) <-> x
                    if isinstance(statement, CompositePropositionNOT):
                        if statement.statement != self.conclusion:
                            assumptions = self.assumptions.get()
                            if not (statement.statement in assumptions):
                                assumptions.append(statement.statement)
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add_step(self.conclusion, Equivalence.NotOfNot, i)
                                    self.proof.extend(proof)
                                    return self.proof, True
                        else:
                            self.proof.add_step(self.conclusion, Equivalence.NotOfNot, i)
                            return self.proof, True

                    # Applying De'Morgan's Law
                    match statement:
                        case CompositePropositionAND(first=first, second=second):
                            if (~first | ~second) != self.conclusion:
                                assumptions = self.assumptions.get()
                                if not ((~first | ~second) in assumptions):
                                    assumptions.append(~first | ~second)
                                    proof, truth = Prover(assumptions, self.conclusion).prove()
                                    if truth:
                                        self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                                        self.proof.extend(proof)
                                        return proof, True
                            else:
                                self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                                return self.proof, True

                        case CompositePropositionOR(first=first, second=second):
                            if ~first & ~second != self.conclusion:
                                assumptions = self.assumptions.get()
                                if not ((~first & ~second) in assumptions):
                                    assumptions.append(~first & ~second)
                                    proof, truth = Prover(assumptions, self.conclusion).prove()
                                    if truth:
                                        self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                                        self.proof.extend(proof)
                                        return self.proof, True
                            else:
                                self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                                return self.proof, True

                case CompositePropositionOR(first=first, second=second):
                    # Applying Resolution
                    if isinstance(self.conclusion, CompositePropositionOR):
                        if self.conclusion.first == first:
                            proof, truth = Prover(self.assumptions.remove(i), ~second | self.conclusion.second).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion, RulesOfInference.Resolution, i, ~second | self.conclusion.second
                            )
                            return self.proof, True
                        if self.conclusion.second == second:
                            proof, truth = Prover(self.assumptions.remove(i), ~first | self.conclusion.first).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion, RulesOfInference.Resolution, i, ~first | self.conclusion.first
                            )
                            return self.proof, True
                        if self.conclusion.first == second:
                            proof, truth = Prover(self.assumptions.remove(i), ~first | self.conclusion.second).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion, RulesOfInference.Resolution, i, ~first | self.conclusion.second
                            )
                            return self.proof, True
                        if self.conclusion.second == first:
                            proof, truth = Prover(self.assumptions.remove(i), ~second | self.conclusion.first).prove()
                            self.proof.extend(proof)
                            self.proof.add_step(
                                self.conclusion, RulesOfInference.Resolution, i, ~second | self.conclusion.first
                            )
                            return self.proof, True

                    # Applying Disjunctive Syllogism
                    if self.conclusion == first:
                        proof, truth = Prover(self.assumptions.remove(i), ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(self.conclusion, RulesOfInference.DisjunctiveSyllogism, i, ~second)
                            return self.proof, True
                    if self.conclusion == second:
                        proof, truth = Prover(self.assumptions.remove(i), ~first).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(self.conclusion, RulesOfInference.DisjunctiveSyllogism, i, ~first)
                            return self.proof, True

                    # Applying De'Morgen's Law
                    if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                        if ~(first.statement & second.statement) != self.conclusion:
                            assumptions = self.assumptions.get()
                            if not (~(first.statement & second.statement) in assumptions):
                                assumptions.append(~(first.statement & second.statement))
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                                    self.proof.extend(proof)
                                    return self.proof, True
                        else:
                            self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                            return self.proof, True

                case CompositePropositionAND(first=first, second=second):
                    # Applying De'Morgen's Law
                    if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                        if ~(first.statement | second.statement) != self.conclusion:
                            assumptions = self.assumptions.get()
                            if not (~(first.statement | second.statement) in assumptions):
                                assumptions.append(~(first.statement | second.statement))
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                                    self.proof.extend(proof)
                                    return self.proof, True
                        else:
                            self.proof.add_step(self.conclusion, Equivalence.DeMorgensLaw, i)
                            return self.proof, True

                    # Applying Simplification
                    assumptions = self.assumptions.get()

                    if first != self.conclusion and second != self.conclusion:
                        if not (first in assumptions) or not (second in assumptions):
                            assumptions.append(first)
                            assumptions.append(second)

                            proof, truth = Prover(assumptions, self.conclusion).prove()
                            if truth:
                                self.proof.add_step(self.conclusion, RulesOfInference.Simplification, i)
                                self.proof.extend(proof)
                                return self.proof, True
                    else:
                        self.proof.add_step(self.conclusion, RulesOfInference.Simplification, i)
                        return self.proof, True

                case CompositePropositionCONDITIONAL(assumption=assumption, conclusion=conclusion):
                    # Applying Modus Ponens
                    if (
                        (not (conclusion in self.assumptions))
                        and self.conclusion != assumption
                        and self.conclusion != ~conclusion
                    ):
                        proof, truth = Prover(self.assumptions.remove(i), assumption).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(conclusion, RulesOfInference.ModusPonens, i, assumption)
                            if self.conclusion != conclusion:
                                proof, truth = Prover(
                                    [conclusion, *(self.assumptions.remove(i).get())], self.conclusion
                                ).prove()
                                if truth:
                                    self.proof.extend(proof)
                                    return self.proof, True
                            else:
                                return self.proof, True

                    # Applying Modus Tollens
                    if (
                        (not (~assumption in self.assumptions))
                        and self.conclusion != ~conclusion
                        and self.conclusion != assumption
                    ):
                        proof, truth = Prover(self.assumptions.remove(i), ~conclusion).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add_step(~assumption, RulesOfInference.ModusTollens, i, ~conclusion)
                            if self.conclusion != ~assumption:
                                proof, truth = Prover(
                                    [~assumption, *(self.assumptions.remove(i).get())], self.conclusion
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

                case CompositePropositionBICONDITIONAL(assumption=assumption, conclusion=conclusion):
                    # Applying definition of Bi-Conditional
                    #  (p <-> q) -> (p -> q) & (q -> p)
                    if (
                        IMPLY(assumption, conclusion) == self.conclusion
                        or IMPLY(conclusion, assumption) == self.conclusion
                    ):
                        self.proof.add_step(self.conclusion, Equivalence.DefinitionOfBiConditional, i)
                        return self.proof, True

                    assumptions = self.assumptions.get()
                    if (not (IMPLY(assumption, conclusion) in assumptions)) or (
                        not (IMPLY(conclusion, assumption) in assumptions)
                    ):
                        proof, truth = Prover(
                            (
                                IMPLY(conclusion, assumption),
                                IMPLY(assumption, conclusion),
                                *self.assumptions.remove(i).assumptions,
                            ),
                            self.conclusion,
                        ).prove()
                        if truth:
                            self.proof.add_step(self.conclusion, Equivalence.DefinitionOfBiConditional, i)
                            self.proof.extend(proof)
                            return self.proof, True

        return self._prove_decomposed_conclusion()
