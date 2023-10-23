import unittest
from logic import Proposition, Prover, IMPLY, IFF

# TODO: check proof


class TestProver(unittest.TestCase):
    def setUp(self) -> None:
        self.x = Proposition("x")
        self.y = Proposition("y")
        self.z = Proposition("z")
        self.p = Proposition("p")
        self.q = Proposition("q")
        self.r = Proposition("r")

    def test_prover_modus_ponens(self):
        assumptions = (
            self.p,
            IMPLY(self.p, self.q),
        )
        conclusion = self.q

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_modus_tollens(self):
        assumptions = (
            ~self.q,
            IMPLY(self.p, self.q),
        )
        conclusion = ~self.p

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_hypothetical_syllogism(self):
        assumptions = (
            IMPLY(self.p, self.q),
            IMPLY(self.q, self.r),
        )
        conclusion = IMPLY(self.p, self.r)

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_disjunctive_syllogism(self):
        # (p ∨ q) ^ ¬ q -> p
        assumptions = (
            self.p | self.q,
            ~self.q,
        )
        conclusion = self.p

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

        # (p ∨ q) ^ ¬ p -> q
        assumptions = (
            self.p | self.q,
            ~self.p,
        )
        conclusion = self.q

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_addition(self):
        assumptions = (self.p,)
        conclusion = self.p | self.q

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

        conclusion = self.r | self.p

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_simplification(self):
        assumptions = (self.p & self.q,)
        conclusion = self.p

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

        conclusion = self.q

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_conjunction(self):
        assumptions = (self.p, self.q)
        conclusion = self.p & self.q

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

        conclusion = self.q & self.p

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_resolution(self):
        assumptions = (
            self.p | self.q,
            ~self.p | self.r,
        )
        conclusion = self.r | self.q

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_demorgans_theorem(self):
        _, truth = Prover(
            (~self.x | ~self.y,),
            ~(self.x & self.y),
        ).prove()
        self.assertTrue(truth)

        _, truth = Prover(
            (~self.x & ~self.y,),
            ~(self.x | self.y),
        ).prove()
        self.assertTrue(truth)

        _, truth = Prover(
            (~(self.x & self.y),),
            ~self.x | ~self.y,
        ).prove()
        self.assertTrue(truth)

        _, truth = Prover(
            (~(self.x | self.y),),
            ~self.x & ~self.y,
        ).prove()
        self.assertTrue(truth)

    def test_prover_not_of_not(self):
        _, truth = Prover((~(~self.p),), self.p).prove()
        self.assertTrue(truth)

    def test_prover_complement(self):
        _, truth = Prover(tuple(), self.p | ~self.p).prove()
        self.assertTrue(truth)

        _, truth = Prover(tuple(), self.p & ~self.p).prove()
        self.assertFalse(truth)

    def test_prover_definition_of_biconditional(self):
        assumption = (IFF(self.p, self.q),)

        conclusion = IMPLY(self.p, self.q)
        _, truth = Prover(assumption, conclusion).prove()
        self.assertTrue(truth)

        conclusion = IMPLY(self.q, self.p)
        _, truth = Prover(assumption, conclusion).prove()
        self.assertTrue(truth)

        assumption = (IMPLY(self.p, self.q), IMPLY(self.q, self.p))

        conclusion = IFF(self.p, self.q)
        _, truth = Prover(assumption, conclusion).prove()
        self.assertTrue(truth)

        conclusion = IFF(self.q, self.p)
        _, truth = Prover(assumption, conclusion).prove()
        self.assertTrue(truth)

    def test_prover_multi_step_1(self):
        # conjunction then demorgans
        assumptions = (~self.x, ~self.y)
        conclusion = ~(self.x | self.y)

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_multi_step_2(self):
        # modus tollens then demorgans
        assumptions = (IMPLY(self.x, self.y), ~self.y)
        conclusion = ~(self.x | self.y)

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prover_multi_step_3(self):
        # modus tollens then demorgans
        assumptions = (IMPLY(self.x, self.y), ~self.y)
        conclusion = ~(self.x | self.y)

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

        assumptions = (IMPLY(self.y | self.z, self.x), ~self.x)
        conclusion = ~self.y & ~self.z

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)

    def test_prove_superman_does_not_exists(self):
        # based on the following question
        # Taken from Discrete Mathematics and Its Applications 7th Edition
        # by Kenneth H. Rosen
        """
        QUESTION:
        If Superman were able and willing to prevent evil,
        he would do so. If Superman were unable to prevent
        evil, he would be impotent; if he were unwilling
        to prevent evil, he would be malevolent. Superman
        does not prevent evil. If Superman exists,
        he is neither impotent nor malevolent.
        Therefore, Superman does not exist.
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

        _, truth = Prover(
            assumptions,
            conclusion,
        ).prove()
        self.assertTrue(truth)


if __name__ == "__main__":
    unittest.main()
