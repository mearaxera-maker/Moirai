```markdown
GMU Technical Specification (v0.2) — purpose-built checklist and measurable targets

Scope and intent
- The GMU is a tightly-scoped augmentation to the CPU/cache hierarchy.
- It targets "small, frequent, and latency-sensitive" memory traffic amenable to generative answers.
- Not intended for bulk data movement, large-model inference, or general-purpose caching.

A. Functional requirements
1. Pattern detection
   - Detect recurring sequences in loads/loads+compute with a temporal window configurable (e.g., 128–4096 micro-ops).
   - Support detection for:
     - Exact repetition (same values)
     - Deterministic transformations (value_n+offset, linear sequences)
     - Small structured arrays (byte/word patterns)
2. Formula construction
   - Construct a compact "formula" that represents the mapping from context to expected output.
   - Formula size budget: typically ≤ 512 bytes (configurable).
3. Generation / response
   - For a matched request, generate a register-aligned response without a main-cache refill.
   - Response correctness probability: configurable confidence threshold (default 99.999% for critical flows).
4. Fail-safe semantics
   - Any uncertain generation must either:
     - Generate a signaled "fallback" to cache/RAM fetch, or
     - Produce a verified value compared against a golden-model check.
   - System determinism guarantee: for safe mode, GMU must not alter program semantics (only accelerate).

B. Performance targets (configurable goals for MVP)
- Added latency for a successful GMU generation: ≤ 1–3 CPU cycles beyond L1 hit time (goal).
- Worst-case additional cost on false-positive generation detection + fallback: bounded and known (metric: < 20 cycles penalty).
- Power budget (per active GMU tile): target 1–20 mW under heavy pattern generation; idle < 10 µW with deep power gating.

C. Capacity and micro-architecture
- Formula Cache:
  - Entry count: target 64–512 entries (configurable per product SKU).
  - Entry metadata: last-used timestamp, confidence, context signature (address+op-hash).
- Patterning Engine:
  - Multi-tier: bit-level filters, byte-level classifiers, stream-level modeling.
  - Router/selector for choosing the active generator (tiny FSM or microcontroller).
- Interface:
  - MMIO registers for status, metrics, and control.
  - ISA hint: __gmu_hint_repetitive (compiler-level attribute).
  - Syscalls/runtime: gmu_register_hint(), gmu_invalidate_formula(), gmu_query_status().

D. Security & trust
- Root-of-trust: per-chip private key securely fused at manufacturing.
- Signed formulas: formula blobs must be signed by the GMU TEE or by a permitted toolchain key.
- Immutable learning kernel: training heuristics and firmware must be immutable except through signed updates.
- Attestation API: host may request a signed attestation of firmware & formula cache metadata.

E. Correctness & verification
- Golden deterministic micro-check: for each generated output a hardware-accessible validator can re-run a deterministic small-model on the output and compare the result (sampling checks for performance).
- Formal verification targets:
  - No unauthorized memory writes by GMU.
  - Deterministic fallback behavior on verification mismatch.
- Fault injection tests: cover worst-case corrupted formula entries and power-failures.

F. Privacy and data handling
- GMU must not write user data to non-volatile storage without host consent.
- Local-only learning by default; any telemetry requires opt-in and must be signed and anonymized.

G. API (candidate)
- __attribute__((gmu_repetitive)) void hot_loop(...) — compiler emits hints.
- int gmu_hint_begin(void *ctx, size_t ctx_len);
- int gmu_hint_end(uint32_t hint_id);
- int gmu_invalidate_hint(uint32_t hint_id);
- int gmu_get_metrics(struct gmu_metrics *m);

H. Acceptance criteria (for MVP)
- Simulator shows >2x latency reduction on at least three realistic microbenchmarks (typing/autocomplete, brush stroke, small-array transform) with energy per operation reduced by at least 30% vs baseline.
- Security flow documented and analyzed (threat model + mitigation).
- Prototype API demonstrated with a small user-space demo.

Design notes & tradeoffs
- Conservative default: GMU must be opt-in per process or region of code.
- The architecture favors auditable, minimal generators rather than Turing-complete ones to keep verification tractable.
```