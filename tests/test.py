import unittest
from logic import Proposition, Prover


class TestProver(unittest.TestCase):
    def test_prover_1(self):
        p = Proposition("p")
        q = Proposition("q")
        propositions = (p, q)
        assumptions = (
            p,
            p % q,
        )

        proof, truth = Prover(
            propositions,
            assumptions,
            q,
        ).prove()
        self.assertTrue(truth)
        # TODO: check proof


if __name__ == "__main__":
    unittest.main()
