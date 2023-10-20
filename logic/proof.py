from typing import Sequence
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


class Proof:
    pass


class Prover:
    def __init__(
        self,
        propositions: Sequence[Proposition],
        assumptions: Sequence[Statement],
        conclusion: Statement,
    ) -> None:
        self.propositions = propositions
        self.assumptions = assumptions
        self.conclusion = conclusion

    def prove(self) -> tuple[Proof, bool]:
        raise NotImplementedError()
