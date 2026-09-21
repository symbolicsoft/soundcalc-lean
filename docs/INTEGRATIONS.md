# Integration prototypes

This branch experiments with two independent integrations. Neither changes what the main
`Soundcalc` library currently claims to prove.

## ArkLib

[ArkLib](https://github.com/Verified-zkEVM/ArkLib) formalizes protocol semantics, coding theory,
and soundness properties. Soundcalc evaluates concrete soundness formulae and aggregates them into
report cells. The intended boundary is:

1. ArkLib proves a protocol-level error bound over an actual finite field and code.
2. A bridge translates its field cardinality, code rate, dimension, and error carrier into
   soundcalc's exact rational parameter model.
3. Soundcalc proves that its computable rational result is a conservative envelope of the
   translated ArkLib bound, then derives security bits and report aggregation.

The dependency remains one-way: the bridge imports ArkLib and Soundcalc. ArkLib does not import
Soundcalc. Concrete reports and deployment policy remain downstream of ArkLib.

### Honest prototype boundary

ArkLib's current Batched-FRI endpoint and Johnson-range MCA theorem contain tracked admissions.
The first bridge must therefore expose provenance explicitly: a result derived from an admitted
ArkLib theorem must not be presented as axiom-clean. The initial target is a proved
unique-decoding Reed--Solomon bound, followed by a separately tracked Johnson-bound bridge.

ArkLib and this repository must use the same Lean and Mathlib release. The prototype pins an exact
ArkLib commit rather than following `main`.

The prototype lives in `SoundcalcArkLib.Bridge`. It provides:

- `uniqueDecodingEnvelopeRat`, the exact quotient in Soundcalc's rational carrier;
- `uniqueDecodingEnvelope_coe_real`, equating that quotient with ArkLib's nonnegative-real
  carrier;
- `CardinalityAgreement` and its reverse quotient rewrite; and
- `rs_mcaError_le_uniqueDecodingEnvelope`, the transported BCIKS20 MCA theorem.

Build it explicitly with `lake build SoundcalcArkLib`; CI builds it in a separate integration
step so ArkLib's unrelated admission warnings do not contaminate Soundcalc's core no-`sorry`
check. An axiom inspection of both the source and transported declarations reports only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`; neither declaration depends on `sorryAx`.
ArkLib's imported dependency cone currently emits warnings for unrelated admitted declarations,
so that declaration-level audit matters more than treating the entire package as axiom-free.

## Clean

[Clean](https://github.com/alabsystems/clean) can independently load and kernel-check selected
Lean `.olean` targets. Run the opt-in experiment after building Clean:

```sh
CLEAN_BIN=/path/to/clean ./scripts/clean-verify.sh
```

The script first builds the `Soundcalc` Lean library, then invokes Clean's
`olean verify-batch --full-validation` path and writes a structured report under
`.lake/clean/` by default. `CLEAN_REPORT` selects another report path and `CLEAN_PARALLEL` controls
target checking parallelism. `CLEAN_INIT_CACHE` selects Clean's versioned Init snapshot directory
(the default is `.lake/clean/init-cache`). For a plumbing smoke test, `CLEAN_LIMIT=N` restricts
verification to the first `N` modules after Clean's dependency ordering; omit it for the intended
full run. Because Soundcalc modules broadly import Mathlib, even a limited run must load a large
dependency closure; the Init snapshot makes later runs cheaper without weakening validation.

A successful report means Clean accepted the selected compiled target values through its full
validation path. It is not source elaboration, proof of compatibility with every Lean feature, or
automatic verification of the complete transitive dependency closure. Clean remains an optional,
independent checker and is not part of Soundcalc's trusted computing base.
