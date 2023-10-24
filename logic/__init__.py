"""Logic is a predicate logic simulator and a automated prover"""

from .proof import Proof, Prover
from .proposition import AND, IFF, IMPLY, NOT, OR, Proposition

__all__ = ["Proposition", "Proof", "Prover", "IMPLY", "IFF", "AND", "OR", "NOT"]
