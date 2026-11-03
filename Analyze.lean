import CRNT.Interop.Analysis

/-!
# The `analyze` executable

A compiled command-line analyzer: it reads a `NetworkData` (or a JSON array of them) from stdin and
writes the corresponding `Analysis` (or array) as JSON to stdout. Because it runs the *compiled*
`NetworkData.analyze`, it produces structural invariants at native speed with no per-network
elaboration — the throughput path for bulk scoring.

**Trust boundary.** This executable uses compiled evaluation (compiler trust), so it lives outside
the kernel-checked guarantees of the `CRNT` library. The library's `analyze_*_eq` bridges relate each reported
field to its propositional definition; for a kernel-checked certificate of a specific network, use
the codegen contract (`docs/generated-certificates.md`) instead.

Usage:

    echo '{"numSpecies":2,"reactions":[{"source":[1,0],"target":[0,1]},
           {"source":[0,1],"target":[1,0]}]}' | lake exe analyze
-/

open CRNT
open Lean (Json fromJson? toJson)

/-- Analyze one network, or each element of a JSON array of networks. -/
def analyzeJson (j : Json) : Except String Json :=
  match j.getArr? with
  | .ok arr => do
      let outs ← arr.mapM fun jn => do
        let d ← fromJson? (α := NetworkData) jn
        pure (toJson d.analyze)
      pure (Json.arr outs)
  | .error _ => do
      let d ← fromJson? (α := NetworkData) j
      pure (toJson d.analyze)

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  match Json.parse input >>= analyzeJson with
  | .ok out => IO.println out.compress
  | .error e =>
      IO.eprintln s!"analyze: invalid NetworkData JSON: {e}"
      IO.Process.exit 1
