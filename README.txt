GMU Ultimate Enhanced TLA+ Spec
=================================

Files:
- GMU_Ultimate_Enhanced.tla : Main specification
- GMU_Ultimate_Enhanced.cfg : Model checker configuration

How to run:
1. Open TLA+ Toolbox.
2. Create a new spec, import GMU_Ultimate_Enhanced.tla.
3. Load GMU_Ultimate_Enhanced.cfg as the model config.
4. Run TLC. Invariants and properties will be checked.

Notes:
- Invariants: NoUseOfQuarantined, GoldenBudgetNonNegative, SafeTelemetry
- Temporal properties: EventuallyQuarantine, ReqCompletes
