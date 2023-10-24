"""Logic is a predicate logic simulator and a automated prover"""

from .proof import Environment, Proof, prove
from .proposition import AND, IFF, IMPLY, NOT, OR, Proposition

__all__ = [
    "Proposition",
    "Proof",
    "Environment",
    "prove",
    "IMPLY",
    "IFF",
    "AND",
    "OR",
    "NOT",
]
