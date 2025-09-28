```markdown
# /proto/enhanced — reference / research TLA+ models

This directory hosts the full-featured specs (e.g., GMU_Ultimate_Enhanced_Full.tla).

Guidance
- These specs are canonical and useful for formal reasoning and property statements.
- Before any TLC run, reduce constants (FORMULA_SLOTS, NUM_REQUESTS) to keep state-space small.
- When porting behavior from enhanced -> run, extract minimal state and add conservative guards (energy reserve, adaptive guard) to preserve deterministic fast-path guarantees.
```
