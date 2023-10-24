"""Tests for the Prover class"""

import unittest

from logic import IFF, IMPLY, prove, Proposition

# TODO: check proof


class TestProver(unittest.TestCase):
    """Tests for the Prover class"""

    def setUp(self) -> None:
        self.x = Proposition("x")
        self.y = Proposition("y")
        self.z = Proposition("z")
        self.p = Proposition("p")
        self.q = Proposition("q")
        self.r = Proposition("r")

    def test_prover_modus_ponens(self):
        """Tests the Modus Ponens rule of inference"""
        assumptions = (
            self.p,
            IMPLY(self.p, self.q),
        )
        conclusion = self.q

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_modus_tollens(self):
        """Tests the Modus Tollens rule of inference"""
        assumptions = (
            ~self.q,
            IMPLY(self.p, self.q),
        )
        conclusion = ~self.p

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_hypothetical_syllogism(self):
        """Tests the Hypothetical Syllogism rule of inference"""
        assumptions = (
            IMPLY(self.p, self.q),
            IMPLY(self.q, self.r),
        )
        conclusion = IMPLY(self.p, self.r)

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_disjunctive_syllogism(self):
        """Tests the Disjunctive Syllogism rule of inference"""
        # (p ∨ q) ^ ¬ q -> p
        assumptions = (
            self.p | self.q,
            ~self.q,
        )
        conclusion = self.p

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

        # (p ∨ q) ^ ¬ p -> q
        assumptions = (
            self.p | self.q,
            ~self.p,
        )
        conclusion = self.q

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_addition(self):
        """Tests the Addition rule of inference"""
        assumptions = (self.p,)
        conclusion = self.p | self.q

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

        conclusion = self.r | self.p

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_simplification(self):
        """Tests the Simplification rule of inference"""
        assumptions = (self.p & self.q,)
        conclusion = self.p

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

        conclusion = self.q

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_conjunction(self):
        """Tests the Conjunction rule of inference"""
        assumptions = (self.p, self.q)
        conclusion = self.p & self.q

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

        conclusion = self.q & self.p

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_resolution(self):
        """Tests the Resolution rule of inference"""
        assumptions = (
            self.p | self.q,
            ~self.p | self.r,
        )
        conclusion = self.r | self.q

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_demorgans_theorem(self):
        """Tests the De'Morgan's Theorem equivalence"""
        _, truth = prove(
            (~self.x | ~self.y,),
            ~(self.x & self.y),
        )
        self.assertTrue(truth)

        _, truth = prove(
            (~self.x & ~self.y,),
            ~(self.x | self.y),
        )
        self.assertTrue(truth)

        _, truth = prove(
            (~(self.x & self.y),),
            ~self.x | ~self.y,
        )
        self.assertTrue(truth)

        _, truth = prove(
            (~(self.x | self.y),),
            ~self.x & ~self.y,
        )
        self.assertTrue(truth)

    def test_prover_not_of_not(self):
        """Tests the Not of Not equivalence"""
        _, truth = prove((~(~self.p),), self.p)
        self.assertTrue(truth)

    def test_prover_complement(self):
        """Tests the Complement equivalence
        i.e. p | ~p is tautology and p & ~p is a contradiction"""
        _, truth = prove(tuple(), self.p | ~self.p)
        self.assertTrue(truth)

        _, truth = prove(tuple(), self.p & ~self.p)
        self.assertFalse(truth)

    def test_prover_definition_of_biconditional(self):
        """Tests the Definition of Bi-Conditional equivalence"""
        assumption = (IFF(self.p, self.q),)

        conclusion = IMPLY(self.p, self.q)
        _, truth = prove(assumption, conclusion)
        self.assertTrue(truth)

        conclusion = IMPLY(self.q, self.p)
        _, truth = prove(assumption, conclusion)
        self.assertTrue(truth)

        assumption = (IMPLY(self.p, self.q), IMPLY(self.q, self.p))

        conclusion = IFF(self.p, self.q)
        _, truth = prove(assumption, conclusion)
        self.assertTrue(truth)

        conclusion = IFF(self.q, self.p)
        _, truth = prove(assumption, conclusion)
        self.assertTrue(truth)

    def test_prover_multi_step_1(self):
        """Tests the multi step proof
        with conjunction then demorgans"""

        assumptions = (~self.x, ~self.y)
        conclusion = ~(self.x | self.y)

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_multi_step_2(self):
        """Tests the multi step proof
        with modus tollens then demorgans"""
        assumptions = (IMPLY(self.x, self.y), ~self.y)
        conclusion = ~(self.x | self.y)

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prover_multi_step_3(self):
        """Tests the multi step proof
        with modus tollens then demorgans"""
        assumptions = (IMPLY(self.x, self.y), ~self.y)
        conclusion = ~(self.x | self.y)

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

        assumptions = (IMPLY(self.y | self.z, self.x), ~self.x)
        conclusion = ~self.y & ~self.z

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)

    def test_prove_superman_does_not_exists(self):
        """Tests the multi step proof

        QUESTION:
        If Superman were able and willing to prevent evil,
        he would do so. If Superman were unable to prevent
        evil, he would be impotent; if he were unwilling
        to prevent evil, he would be malevolent. Superman
        does not prevent evil. If Superman exists,
        he is neither impotent nor malevolent.
        Therefore, Superman does not exist.

        Taken from Discrete Mathematics and Its Applications 7th Edition
        by Kenneth H. Rosen
        """

        a = Proposition("a", "Superman is able to prevent evil")
        b = Proposition("b", "Superman is willing to prevent evil")
        c = Proposition("c", "Superman is impotent")
        d = Proposition("d", "Superman is malevolent")
        e = Proposition("f", "Superman prevents evil")
        f = Proposition("g", "Superman exists")

        assumptions = [
            IMPLY(a & b, e),
            IMPLY(~e, c),
            IMPLY(~b, d),
            ~e,
            IMPLY(f, ~c & ~d),
        ]
        conclusion = ~f

        _, truth = prove(
            assumptions,
            conclusion,
        )
        self.assertTrue(truth)


if __name__ == "__main__":
    unittest.main()
