from typing import Sequence, Generator, Iterator, TypeAlias
from .proposition import *

from enum import Enum

AssumptionT: TypeAlias = "Assumption"


class RulesOfInference(Enum):
    ModusPonens = "Modus Ponens"
    ModusTollens = "Modus Tollens"
    HypotheticalSyllogism = "Hypothetical Syllogism"
    DisjunctiveSyllogism = "Disjunctive Syllogism"
    Addition = "Addition"
    Simplification = "Simplification"
    Conjunction = "Conjunction"
    Resolution = "Resolution"
    Deduction = "Deduction"
    DefinitionOfBiConditional = "Definition Of Bi-Conditional"
    DeMorgensLaw = "De'Morgen's Law"


class Assumption:
    def __init__(self, assumptions: Sequence[Statement] | Self) -> None:
        if isinstance(assumptions, Assumption):
            self.assumptions: set[Statement] = set(assumptions.assumptions)
        else:
            self.assumptions = set(assumptions)

    def __contains__(self, key: Any) -> bool:
        return key in self.assumptions

    def with_proposition(self, prop: Statement) -> Generator[Statement, None, None]:
        l = prop.extract()
        for i in self.assumptions:
            yielded = False
            for j in l:
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
    def __init__(self) -> None:
        self.proof: list[tuple[RulesOfInference, tuple[Statement, ...]]] = []

    def add(self, roi: RulesOfInference, *statement: Statement) -> None:
        self.proof.append((roi, (*statement,)))

    def extend(self, proof: Self) -> None:
        self.proof.extend(proof.proof)

    def __iter__(self) -> Iterator[tuple[RulesOfInference, tuple[Statement, ...]]]:
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
        # if not isinstance(conclusion, Proposition):
        #     raise NotImplementedError(
        #         "Proving where the conclusion is Composite Proposition is not yet implemented."
        #     )

        if isinstance(assumptions, Assumption):
            self.assumptions = assumptions
        else:
            self.assumptions = Assumption(assumptions)
        self.conclusion = conclusion
        self.proof = Proof()

    def _prove_decomposed_conclusion(self) -> tuple[Proof, bool]:
        match self.conclusion:
            case CompositePropositionAND(first=first, second=second):
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
                        self.proof.add(RulesOfInference.DeMorgensLaw, ~(first | second))
                        return self.proof, True

            case CompositePropositionOR(first=first, second=second):
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
                        self.proof.add(RulesOfInference.DeMorgensLaw, ~(first & second))
                        return self.proof, True

            case CompositePropositionBICONDITIONAL(assumption=assumption, conclusion=conclusion):
                # Applying definition of Bi-Conditional
                #  (p <-> q) -> (p -> q) & (q -> p)
                proof_p_implies_q, truth_p_implies_q = Prover(
                    self.assumptions.remove(self.conclusion), assumption / conclusion
                ).prove()
                proof_q_implies_p, truth_q_implies_p = Prover(
                    self.assumptions.remove(self.conclusion), conclusion / assumption
                ).prove()
                if truth_p_implies_q and truth_q_implies_p:
                    self.proof.extend(proof_p_implies_q)
                    self.proof.extend(proof_q_implies_p)
                    self.proof.add(
                        RulesOfInference.DefinitionOfBiConditional,
                        assumption / conclusion,
                        conclusion / assumption,
                    )
                    return self.proof, True

            case CompositePropositionNOT(statement=statement):
                # Applying De'Morgen's Law
                match statement:
                    case CompositePropositionAND(first=first, second=second):
                        proof, truth = Prover(self.assumptions, ~first | ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.DeMorgensLaw, ~first | ~second)
                            return self.proof, True
                    case CompositePropositionOR(first=first, second=second):
                        proof, truth = Prover(self.assumptions, ~first & ~second).prove()
                        if truth:
                            self.proof.extend(proof)
                            self.proof.add(RulesOfInference.DeMorgensLaw, ~first & ~second)
                            return self.proof, True

        return Proof(), False

    def prove(self) -> tuple[Proof, bool]:
        for i in self.assumptions.with_proposition(self.conclusion):
            if i == self.conclusion:
                self.proof.add(RulesOfInference.Deduction, i)
                return self.proof, True

            match i:
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
                                self.conclusion.assumption / assumption,
                            ).prove()
                            if truth:
                                self.proof.extend(proof)
                                self.proof.add(RulesOfInference.HypotheticalSyllogism, i)
                                return self.proof, True

                case CompositePropositionOR(first=first, second=second):
                    # Applying Resolution
                    if isinstance(self.conclusion, CompositePropositionOR):
                        if self.conclusion.first == first:
                            proof, truth = Prover(self.assumptions.remove(i), ~second | self.conclusion.second).prove()
                            self.proof.add(RulesOfInference.Resolution, i)
                            self.proof.extend(proof)
                            return self.proof, True
                        if self.conclusion.second == second:
                            proof, truth = Prover(self.assumptions.remove(i), ~first | self.conclusion.first).prove()
                            self.proof.add(RulesOfInference.Resolution, i)
                            self.proof.extend(proof)
                            return self.proof, True
                        if self.conclusion.first == second:
                            proof, truth = Prover(self.assumptions.remove(i), ~first | self.conclusion.second).prove()
                            self.proof.add(RulesOfInference.Resolution, i)
                            self.proof.extend(proof)
                            return self.proof, True
                        if self.conclusion.second == first:
                            proof, truth = Prover(self.assumptions.remove(i), ~second | self.conclusion.first).prove()
                            self.proof.add(RulesOfInference.Resolution, i)
                            self.proof.extend(proof)
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
                                self.proof.add(RulesOfInference.DeMorgensLaw, i)
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
                                self.proof.add(RulesOfInference.DeMorgensLaw, i)
                                self.proof.extend(proof)
                                return self.proof, True

                case CompositePropositionBICONDITIONAL(assumption=assumption, conclusion=conclusion):
                    # Applying definition of Bi-Conditional
                    #  (p <-> q) -> (p -> q) & (q -> p)
                    assumptions = self.assumptions.get()
                    if not ((assumption / conclusion) in assumptions) or not ((conclusion / assumption) in assumptions):
                        assumptions.append(assumption / conclusion)
                        assumptions.append(conclusion / assumption)

                        proof, truth = Prover(assumptions, self.conclusion).prove()
                        if truth:
                            self.proof.add(RulesOfInference.DefinitionOfBiConditional, i)
                            self.proof.extend(proof)
                            return self.proof, True

                case CompositePropositionNOT(statement=statement):
                    # Applying De'Morgan's Law
                    match statement:
                        case CompositePropositionAND(first=first, second=second):
                            assumptions = self.assumptions.get()
                            if not ((~first | ~second) in assumptions):
                                assumptions.append(~first | ~second)
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add(RulesOfInference.DeMorgensLaw, i)
                                    self.proof.extend(proof)
                                    return proof, True
                        case CompositePropositionOR(first=first, second=second):
                            assumptions = self.assumptions.get()
                            if not ((~first & ~second) in assumptions):
                                assumptions.append(~first & ~second)
                                proof, truth = Prover(assumptions, self.conclusion).prove()
                                if truth:
                                    self.proof.add(RulesOfInference.DeMorgensLaw, i)
                                    self.proof.extend(proof)
                                    return self.proof, True

        return self._prove_decomposed_conclusion()
