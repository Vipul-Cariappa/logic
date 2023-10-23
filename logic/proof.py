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


class Equivalence(ProofStrategy):
    DefinitionOfBiConditional = "Definition Of Bi-Conditional"
    DeMorgensLaw = "De'Morgen's Law"
    NotOfNot = "NotOfNot"
    Complement = "Complement"


class RulesOfInference(ProofStrategy):
    ModusPonens = "Modus Ponens"
    ModusTollens = "Modus Tollens"
    HypotheticalSyllogism = "Hypothetical Syllogism"
    DisjunctiveSyllogism = "Disjunctive Syllogism"
    Addition = "Addition"
    Simplification = "Simplification"
    Conjunction = "Conjunction"
    Resolution = "Resolution"
    Deduction = "Deduction"


class Assumption:
    def __init__(self, assumptions: Sequence[Statement] | AssumptionT) -> None:
        if isinstance(assumptions, Assumption):
            self.assumptions: set[Statement] = set(assumptions.assumptions)
        else:
            self.assumptions = set(assumptions)

    def __contains__(self, key: Any) -> bool:
        return key in self.assumptions

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
    def __init__(self, proof: list[tuple[ProofStrategy, tuple[Statement, ...]]] | None = None) -> None:
        self.proof: list[tuple[ProofStrategy, tuple[Statement, ...]]] = proof if proof else []

    def add(self, roi: ProofStrategy, *statement: Statement) -> None:
        self.proof.append((roi, (*statement,)))

    def extend(self, proof: ProofT) -> None:
        self.proof.extend(proof.proof)

    def __iter__(self) -> Iterator[tuple[ProofStrategy, tuple[Statement, ...]]]:
        return iter(self.proof)

    def __str__(self) -> str:
        result = ""
        for rof, statements in self:
            result += str(rof) + "\t"
            result += "{" + ", ".join(str(i) for i in statements) + "}"
            result += "\n"
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
                        self.proof.add(Equivalence.NotOfNot, statement.statement)
                        return self.proof, True

                # Applying De'Morgen's Law
                match statement:
                    case CompositePropositionAND(first=first, second=second):
                        proof, truth = Prover(self.assumptions, ~first | ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add(Equivalence.DeMorgensLaw, ~first | ~second)
                            return self.proof, True
                    case CompositePropositionOR(first=first, second=second):
                        proof, truth = Prover(self.assumptions, ~first & ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add(Equivalence.DeMorgensLaw, ~first & ~second)
                            return self.proof, True

            case CompositePropositionOR(first=first, second=second):
                # Applying x | ~x <-> True
                if first == ~second or ~first == second:
                    return Proof([(Equivalence.Complement, (self.conclusion,))]), True

                # Applying Addition
                proof_first, truth_first = Prover(self.assumptions.remove(self.conclusion), first).prove()
                if truth_first:
                    self.proof.extend(proof_first)
                    self.proof.add(RulesOfInference.Addition, first, second)
                    return self.proof, True
                proof_second, truth_second = Prover(self.assumptions.remove(self.conclusion), second).prove()
                if truth_second:
                    self.proof.extend(proof_second)
                    self.proof.add(RulesOfInference.Addition, second, first)
                    return self.proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                    proof, truth = Prover(self.assumptions, ~(first & second)).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add(Equivalence.DeMorgensLaw, ~(first & second))
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
                    self.proof.add(RulesOfInference.Conjunction, first, second)
                    return self.proof, True

                # Applying De'Morgen's Law
                if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                    proof, truth = Prover(self.assumptions, ~(first | second)).prove()
                    if truth:
                        self.proof.extend(proof)
                        self.proof.add(Equivalence.DeMorgensLaw, ~(first | second))
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
                    self.proof.add(
                        Equivalence.DefinitionOfBiConditional,
                        IMPLY(assumption, conclusion),
                        IMPLY(conclusion, assumption),
                    )
                    return self.proof, True

        return Proof(), False

    def prove(self) -> tuple[Proof, bool]:
        for i in self.assumptions.with_proposition(self.conclusion):
            if i == self.conclusion:
                self.proof.add(RulesOfInference.Deduction, i)
                return self.proof, True

            match i:
                case CompositePropositionNOT(statement=statement):
                    # Applying NotOfNot i.e. ~(~x) <-> x
                    if isinstance(statement, CompositePropositionNOT):
                        assumptions = self.assumptions.get()
                        if not (statement.statement in assumptions):
                            assumptions.append(statement.statement)
                            proof, truth = Prover(assumptions, self.conclusion).prove()
                            if truth:
                                self.proof.add(Equivalence.NotOfNot, i)
                                self.proof.extend(proof)
                                return self.proof, True

                    # Applying De'Morgan's Law
                    match statement:
                        case CompositePropositionAND(first=first, second=second):
                            assumptions = self.assumptions.get()
                            if not ((~first | ~second) in assumptions):
                                assumptions.append(~first | ~second)
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add(Equivalence.DeMorgensLaw, i)
                                    self.proof.extend(proof)
                                    return proof, True
                        case CompositePropositionOR(first=first, second=second):
                            assumptions = self.assumptions.get()
                            if not ((~first & ~second) in assumptions):
                                assumptions.append(~first & ~second)
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add(Equivalence.DeMorgensLaw, i)
                                    self.proof.extend(proof)
                                    return self.proof, True

                case CompositePropositionOR(first=first, second=second):
                    # Applying Resolution
                    if isinstance(self.conclusion, CompositePropositionOR):
                        if self.conclusion.first == first:
                            proof, truth = Prover(self.assumptions.remove(i), ~second | self.conclusion.second).prove()
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.Resolution, i)
                            return self.proof, True
                        if self.conclusion.second == second:
                            proof, truth = Prover(self.assumptions.remove(i), ~first | self.conclusion.first).prove()
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.Resolution, i)
                            return self.proof, True
                        if self.conclusion.first == second:
                            proof, truth = Prover(self.assumptions.remove(i), ~first | self.conclusion.second).prove()
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.Resolution, i)
                            return self.proof, True
                        if self.conclusion.second == first:
                            proof, truth = Prover(self.assumptions.remove(i), ~second | self.conclusion.first).prove()
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.Resolution, i)
                            return self.proof, True

                    # Applying Disjunctive Syllogism
                    if self.conclusion == first:
                        proof, truth = Prover(self.assumptions.remove(i), ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.DisjunctiveSyllogism, i)
                            return self.proof, True
                    if self.conclusion == second:
                        proof, truth = Prover(self.assumptions.remove(i), ~first).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.DisjunctiveSyllogism, i)
                            return self.proof, True

                    # Applying De'Morgen's Law
                    if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                        assumptions = self.assumptions.get()
                        if not (~(first.statement & second.statement) in assumptions):
                            assumptions.append(~(first.statement & second.statement))
                            proof, truth = Prover(assumptions, self.conclusion).prove()
                            if truth:
                                self.proof.add(Equivalence.DeMorgensLaw, i)
                                self.proof.extend(proof)
                                return self.proof, True

                case CompositePropositionAND(first=first, second=second):
                    # Applying Simplification
                    assumptions = self.assumptions.get()

                    if not (first in assumptions) or not (second in assumptions):
                        assumptions.append(first)
                        assumptions.append(second)

                        proof, truth = Prover(assumptions, self.conclusion).prove()
                        if truth:
                            self.proof.add(RulesOfInference.Simplification, i)
                            self.proof.extend(proof)
                            return self.proof, True

                    # Applying De'Morgen's Law
                    if isinstance(first, CompositePropositionNOT) and isinstance(second, CompositePropositionNOT):
                        assumptions = self.assumptions.get()
                        if not (~(first.statement | second.statement) in assumptions):
                            assumptions.append(~(first.statement | second.statement))
                            proof, truth = Prover(assumptions, self.conclusion).prove()
                            if truth:
                                self.proof.add(Equivalence.DeMorgensLaw, i)
                                self.proof.extend(proof)
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
                            self.proof.add(RulesOfInference.ModusPonens, i, assumption)
                            proof, truth = Prover(
                                [conclusion, *(self.assumptions.remove(i).get())], self.conclusion
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
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
                            self.proof.add(RulesOfInference.ModusTollens, i, ~conclusion)
                            proof, truth = Prover(
                                [~assumption, *(self.assumptions.remove(i).get())], self.conclusion
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
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
                                self.proof.add(RulesOfInference.HypotheticalSyllogism, i)
                                return self.proof, True

                case CompositePropositionBICONDITIONAL(assumption=assumption, conclusion=conclusion):
                    # Applying definition of Bi-Conditional
                    #  (p <-> q) -> (p -> q) & (q -> p)
                    assumptions = self.assumptions.get()
                    if not (IMPLY(assumption, conclusion) in assumptions) or not (
                        IMPLY(conclusion, assumption) in assumptions
                    ):
                        assumptions.append(IMPLY(assumption, conclusion))
                        assumptions.append(IMPLY(conclusion, assumption))

                        proof, truth = Prover(assumptions, self.conclusion).prove()
                        if truth:
                            self.proof.add(Equivalence.DefinitionOfBiConditional, i)
                            self.proof.extend(proof)
                            return self.proof, True

        return self._prove_decomposed_conclusion()
