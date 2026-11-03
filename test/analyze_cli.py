"""Exercise the compiled analyzer, including both sides of the siphon verdicts.

Run after `lake build analyze`: python3 -m unittest discover -s test -p '*_cli.py'.
"""

import json
from pathlib import Path
import subprocess
import unittest


ROOT = Path(__file__).resolve().parents[1]
ANALYZE = ROOT / ".lake" / "build" / "bin" / "analyze"


def network(num_species, *reactions):
    return {
        "numSpecies": num_species,
        "reactions": [
            {"source": source, "target": target} for source, target in reactions
        ],
    }


class AnalyzeCLI(unittest.TestCase):
    def invoke(self, payload):
        return subprocess.run(
            [str(ANALYZE)], input=payload, text=True, capture_output=True,
            timeout=30, cwd=ROOT,
        )

    def analyze(self, data):
        result = self.invoke(json.dumps(data))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, "")
        return json.loads(result.stdout)

    def test_reversible_pair(self):
        actual = self.analyze(network(2, ([1, 0], [0, 1]), ([0, 1], [1, 0])))
        expected = {
            "version": 19, "numSpecies": 2, "numReactions": 2, "numComplexes": 2,
            "numLinkageClasses": 1, "stoichRank": 1, "deficiency": 0,
            "conservationLawDim": 1, "weaklyReversible": True,
            "hasCriticalSiphon": False, "persistenceCertified": True,
            "noPositivePeriodicOrbitCertified": True, "stoichRankTwo": False,
            "noDrainableSiphon": True, "noSelfReplicableSiphon": True,
            "minimalCriticalSiphonDichotomy": True, "persistenceSiphonDichotomy": True,
        }
        self.assertEqual({key: actual[key] for key in expected}, expected)

    def test_drainable_and_self_replicable_siphons(self):
        # 2A -> A can drain the only siphon; A -> 2A can replicate it. Reversing
        # both reactions admits both behaviors, so both exclusion flags must be false.
        cases = [
            (network(1, ([2], [1])), False, True),
            (network(1, ([1], [2])), True, False),
            (network(1, ([2], [1]), ([1], [2])), False, False),
        ]
        for data, no_drain, no_replicate in cases:
            with self.subTest(data=data):
                actual = self.analyze(data)
                self.assertEqual(actual["noDrainableSiphon"], no_drain)
                self.assertEqual(actual["noSelfReplicableSiphon"], no_replicate)
                self.assertTrue(actual["hasCriticalSiphon"])
                self.assertTrue(actual["minimalCriticalSiphonDichotomy"])
                self.assertFalse(actual["persistenceSiphonDichotomy"])

    def test_batch_matches_single_analysis(self):
        inputs = [network(0), network(1, ([1], [2]))]
        self.assertEqual(self.analyze(inputs), [self.analyze(data) for data in inputs])

    def test_empty_network(self):
        actual = self.analyze(network(0))
        self.assertEqual(actual["stoichRank"], 0)
        self.assertEqual(actual["deficiency"], 0)
        self.assertIsNone(actual["hopfBoundaryMargin"])
        self.assertIsNone(actual["gershgorinStabilityMargin"])
        self.assertIsNone(actual["gershgorinColStabilityMargin"])

    def test_invalid_input(self):
        for payload in ("{", '{"numSpecies":-1,"reactions":[]}', "[{}]"):
            with self.subTest(payload=payload):
                result = self.invoke(payload)
                self.assertEqual(result.returncode, 1)
                self.assertEqual(result.stdout, "")
                self.assertIn("analyze: invalid NetworkData JSON:", result.stderr)


if __name__ == "__main__":
    unittest.main()
