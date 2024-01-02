"""Logic is a predicate logic simulator and a automated prover"""

from .proof import Environment, Proof, prove
from .proposition import (
    AND,
    FORALL,
    IFF,
    IMPLY,
    NOT,
    OR,
    THEREEXISTS,
    Predicate,
    Proposition,
)

__all__ = [
    "Predicate",
    "Proposition",
    "Proof",
    "Environment",
    "prove",
    "IMPLY",
    "IFF",
    "AND",
    "OR",
    "NOT",
    "FORALL",
    "THEREEXISTS",
]
