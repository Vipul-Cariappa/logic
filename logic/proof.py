from typing import Sequence, Generator, Self, Iterator
from .proposition import (
    Proposition,
    CompositeProposition,
    CompositePropositionAND,
    CompositePropositionBICONDITIONAL,
    CompositePropositionCONDITIONAL,
    CompositePropositionNOT,
    CompositePropositionOR,
    Statement,
)

from enum import Enum


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


class Assumption:
    def __init__(self, assumptions: Sequence[Statement] | Self) -> None:
        if isinstance(assumptions, Assumption):
            self.assumptions: Sequence[Statement] = list(assumptions.assumptions)
        else:
            self.assumptions = list(assumptions)

        # for i in assumptions:
        #     match i:
        #         case CompositePropositionAND(first=first, second=second):
        #             self.assumptions.append(first)
        #             self.assumptions.append(second)
        #         case CompositePropositionBICONDITIONAL(
        #             assumption=assumption, conclusion=conclusion
        #         ):
        #             self.assumptions.append(assumption / conclusion)
        #             self.assumptions.append(conclusion / assumption)

    def with_proposition(self, prop: Statement) -> Generator[Statement, None, None]:
        l = prop.extract()
        for i in self.assumptions:
            yielded = False
            for j in l:
                if j in i:
                    yielded = True
                    yield i

            if not yielded and prop in i:
                yield i


class Proof:
    def __init__(self) -> None:
        self.proof: list[tuple[RulesOfInference, Statement]] = []

    def add(self, roi: RulesOfInference, statement: Statement) -> None:
        self.proof.append((roi, statement))

    def extend(self, proof: Self) -> None:
        self.proof.extend(proof.proof)

    def __iter__(self) -> Iterator[tuple[RulesOfInference, Statement]]:
        return reversed(self.proof)

    def __str__(self) -> str:
        return "\n".join(f"{str(i[0])}\t{{{str(i[1])}}}" for i in self)


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

    def prove(self) -> tuple[Proof, bool]:
        for i in self.assumptions.with_proposition(self.conclusion):
            if i == self.conclusion:
                self.proof.add(RulesOfInference.Deduction, i)
                return self.proof, True

            match i:
                case CompositePropositionCONDITIONAL(
                    assumption=assumption, conclusion=conclusion
                ):
                    # Applying Modus Ponens
                    if conclusion == self.conclusion:
                        proof, truth = Prover(self.assumptions, assumption).prove()
                        if truth:
                            self.proof.add(RulesOfInference.ModusPonens, i)
                            self.proof.extend(proof)
                            return self.proof, True

                    # Applying Modus Tollens
                    if ~assumption == self.conclusion:
                        proof, truth = Prover(self.assumptions, ~conclusion).prove()
                        if truth:
                            self.proof.add(RulesOfInference.ModusTollens, i)
                            self.proof.extend(proof)
                            return self.proof, True

        return Proof(), False
