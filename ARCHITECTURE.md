```markdown
Architecture overview — components, interactions, and integration points

Block diagram (conceptual)
[CPU core] <-> [L1] <-> [GMU (Generative Core + Formula Cache + Pattern Engine)] <-> [L2/L3] <-> [DRAM]
                          ^
                          |
                      Power/PMU, Security Root

Component responsibilities
1. Pattern Engine (snoop + classifier)
   - Observes load/store streams and minimal CPU context (PC hash, small register snapshot).
   - Builds candidate formulas and scores them.

2. Formula Cache
   - Stores compact formulas and metadata.
   - Fast lookup by address+context signature.
   - Eviction policy tuned for temporal locality.

3. Generative Core
   - Executes a compact, audited sequence that produces the requested data.
   - Constrained instruction set or microcode for safety.

4. Runtime (OS / AI Core)
   - Provides hooks for developer hints and non-invasive runtime profiling.
   - Manages per-process enabling, and formula lifetime.

Integration points
- Compiler: emits hints and optionally inline generation descriptors.
- OS kernel: handles privileges for formula signing & revocation.
- Application: opt-in pragmas or runtime hints to accelerate hot loops.

Power management
- Aggressive power gating with microsecond wake-up.
- Heuristics to avoid wake churn; warm-up windows for suspected patterns.

Integration sketch for a Snapdragon-style SoC
- GMU can be a chiplet or NPU sub-block with a low-latency link to the CPU core complex.
- Tight timing: place physically near CPU caches to reduce interconnect latency.
- Managed by Qualcomm-style AI Engine orchestration layer (if ported to that vendor).

Notes on verifiability & observability
- Provide hardware counters, formula logs, and an "explain" API that returns the formula and the context for any generated value.
- This is critical for debugging and adoption.

Open questions
- How much context (register snapshot) is safe/necessary to capture?
- What is the minimal expressiveness for formula representation that balances coverage and verifiability?
- Exact power/area budget per SKU — set during silicon planning.
```