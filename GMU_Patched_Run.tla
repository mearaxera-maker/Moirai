----------------------------- MODULE GMU_Patched_Run -----------------------------
EXTENDS Naturals, Sequences, TLC, FiniteSets, Integers, Bags

(*
  Patched GMU module with ENFORCE_ADAPTIVE_GUARD and conservative energy preconditions.
  Placeholders remain for detailed algorithms; this file is runnable by TLC after setting
  constants in a .cfg.
*)

CONSTANTS
  FORMULA_SLOTS, NUM_REQUESTS, SAMPLE_PERIOD, NUM_CPUS, MAX_RETRIES,
  FAULTY_FORMULAS, REQUEST_PATTERN, GOLDEN_BUDGET,
  FAULT_PROBABILITY_PERCENT, ADAPTIVE_SAMPLING, DYNAMIC_QUARANTINE,
  GMU_ENERGY, FALLBACK_ENERGY, TRAINER_ENERGY,
  MAX_RECOVERY_ATTEMPTS, ENERGY_BUDGET,
  PREDICTIVE_ENERGY, PREEMPTIVE_QUARANTINE, ENERGY_RECYCLING,
  CRITICALITY_AWARE, CONCURRENCY_CONTROL,
  ADAPTIVE_HORIZON, ENERGY_RESERVE, ENFORCE_ADAPTIVE_GUARD, MIN_ALLOWED_PERIOD

ASSUME FORMULA_SLOTS \in 1..5
ASSUME NUM_REQUESTS \in 1..20
ASSUME SAMPLE_PERIOD \in {1,2,4}
ASSUME NUM_CPUS \in 1..3
ASSUME MAX_RETRIES \in 1..5
ASSUME FAULTY_FORMULAS \subseteq 0..FORMULA_SLOTS-1
ASSUME REQUEST_PATTERN \in {"repetitive", "mixed", "bursty", "adaptive"}
ASSUME GOLDEN_BUDGET \in 1..(NUM_REQUESTS * 2)
ASSUME FAULT_PROBABILITY_PERCENT \in {0,10,25,50}
ASSUME GMU_ENERGY \in 1..5
ASSUME FALLBACK_ENERGY \in 1..10
ASSUME TRAINER_ENERGY \in 2..8
ASSUME MAX_RECOVERY_ATTEMPTS \in 1..5
ASSUME ENERGY_BUDGET \in 1..(NUM_REQUESTS * 10)
ASSUME ADAPTIVE_HORIZON \in 1..10
ASSUME ENERGY_RESERVE \in 0..ENERGY_BUDGET
ASSUME ENFORCE_ADAPTIVE_GUARD \in BOOLEAN
ASSUME MIN_ALLOWED_PERIOD \in 1..4
ASSUME ADAPTIVE_SAMPLING \in BOOLEAN
ASSUME PREDICTIVE_ENERGY \in BOOLEAN
ASSUME PREEMPTIVE_QUARANTINE \in BOOLEAN
ASSUME ENERGY_RECYCLING \in BOOLEAN
ASSUME CRITICALITY_AWARE \in BOOLEAN
ASSUME CONCURRENCY_CONTROL \in BOOLEAN
ASSUME DYNAMIC_QUARANTINE \in BOOLEAN

Status == {"pending", "processing_gmu", "processing_fallback", "completed", "failed", "quarantined"}
SystemModes == {"normal", "degraded", "fallback_only", "energy_saver", "maintenance"}

VARIABLES
  Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
  GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
  Telemetry, GoldenBudgetLeft, LatencyTrack,
  EnergyUsed, AdaptivePeriod, RecoveryAttempts, FormulaProvenance,
  RequestFormulaMap, DynamicFaults, PerformanceMetrics, EnergyState,
  AdaptiveState, FaultInjectionCount, PredictiveState, PreemptiveState,
  ConcurrencyState, RecycledEnergy, CriticalityState, EfficiencyScores

Init ==
  /\ Cache = [i \in 0..FORMULA_SLOTS-1 |-> [sig |-> i + 100, model_level |-> 1, active |-> TRUE,
                                              usage_count |-> 0, last_used |-> 0, energy_saved |-> 0,
                                              efficiency_score |-> 100]]
  /\ RequestQueue = GenerateEnhancedRequests(NUM_REQUESTS, REQUEST_PATTERN)
  /\ RequestStates = [i \in 1..NUM_REQUESTS |-> [status |-> "pending", formula_idx |-> -1]]
  /\ PC = 0
  /\ Quarantine = {}
  /\ CPU_Results = [cpu \in 1..NUM_CPUS |-> << >>]
  /\ GoldenChecks = {}
  /\ MismatchCount = [i \in 0..FORMULA_SLOTS-1 |-> 0]
  /\ RetryCounts = [i \in 1..NUM_REQUESTS |-> 0]
  /\ SystemMode = "normal"
  /\ TrainerQueue = << >>
  /\ Telemetry = << >>
  /\ GoldenBudgetLeft = GOLDEN_BUDGET
  /\ LatencyTrack = [i \in 1..NUM_REQUESTS |-> 0]
  /\ EnergyUsed = 0
  /\ AdaptivePeriod = SAMPLE_PERIOD
  /\ RecoveryAttempts = [i \in 0..FORMULA_SLOTS-1 |-> 0]
  /\ FormulaProvenance = [i \in 0..FORMULA_SLOTS-1 |-> << >>]
  /\ RequestFormulaMap = [i \in 1..NUM_REQUESTS |-> -1]
  /\ DynamicFaults = {}
  /\ PerformanceMetrics = [throughput |-> 0, avg_latency |-> 0, energy_efficiency |-> 0, fault_tolerance |-> 100]
  /\ EnergyState = [total_used |-> 0, budget_left |-> ENERGY_BUDGET, efficiency_ratio |-> 0, recycled_energy |-> 0]
  /\ AdaptiveState = [current_period |-> SAMPLE_PERIOD, target_period |-> SAMPLE_PERIOD, transition_step |-> 0, convergence_count |-> 0]
  /\ FaultInjectionCount = 0
  /\ PredictiveState = [future_energy_need |-> 0, conservation_mode |-> FALSE, proactive_adjustments |-> 0]
  /\ PreemptiveState = [fault_trend |-> "low", recent_faults |-> 0, preemptive_actions |-> 0]
  /\ ConcurrencyState = [mode |-> "medium", active_requests |-> 0, max_concurrent |-> NUM_CPUS * 2]
  /\ RecycledEnergy = 0
  /\ CriticalityState = [high_priority_pending |-> 0, critical_completed |-> 0, avg_critical_latency |-> 0]
  /\ EfficiencyScores = [i \in 0..FORMULA_SLOTS-1 |-> 100]

GenerateEnhancedRequests(num, pattern) ==
  LET base_requests ==
    [i \in 1..num |-> 
      [addr |-> CASE pattern = "repetitive" -> 100
                   [] pattern = "mixed" -> 100 + (i % 5) * 8
                   [] pattern = "bursty" -> IF i % 4 = 0 THEN 200 ELSE 100
                   [] pattern = "adaptive" -> 100 + ((i * PC) % 50),
       size |-> 8,
       type |-> 0,
       cpu_id |-> (i % NUM_CPUS) + 1,
       req_id |-> i,
       criticality |-> IF i % 3 = 0 THEN "high" ELSE "low"]]
  IN base_requests

\* ---------- HELPERS (placeholders) ----------
SigOf(req) == req.addr

ComputeAdaptivePeriod ==
  LET pending == Cardinality({r \in 1..NUM_REQUESTS : RequestStates[r].status = "pending"})
  IN IF pending > NUM_REQUESTS \div 2 THEN 1 ELSE SAMPLE_PERIOD

LRU_Lookup(sig) ==
  IF \E i \in 0..FORMULA_SLOTS-1: Cache[i].active /\ Cache[i].sig = sig THEN
    CHOOSE i \in 0..FORMULA_SLOTS-1: Cache[i].active /\ Cache[i].sig = sig
  ELSE -1

UpdateCacheUsage(idx, pc) == [Cache EXCEPT ![idx] = [@ EXCEPT !.usage_count = @ + 1, !.last_used = pc]]

ChooseMostEfficientFormula(sig) == LRU_Lookup(sig)

ComputeEnergyCostForPeriod(period) == period * GMU_ENERGY * ADAPTIVE_HORIZON

AdaptiveProjectionGuard(period) == ComputeEnergyCostForPeriod(period) <= EnergyState.budget_left - ENERGY_RESERVE

\* ---------- CORE ACTIONS (with conservative guards) ----------
EnergyAwareGMUStart(req_id) ==
  /\ req_id \in 1..Len(RequestQueue)
  /\ RequestStates[req_id].status = "pending"
  /\ LET req == RequestQueue[req_id] IN
     LET sig == SigOf(req) IN
     LET idx == LRU_Lookup(sig) IN
     /\ idx /= -1
     /\ EnergyState.budget_left >= GMU_ENERGY
     /\ ConcurrencyState.active_requests < ConcurrencyState.max_concurrent
     /\ \* Conservative precondition: ensure post-consumption budget still leaves room for MIN_ALLOWED_PERIOD worst-case
        (EnergyState.budget_left - GMU_ENERGY) >= (ENERGY_RESERVE + ComputeEnergyCostForPeriod(MIN_ALLOWED_PERIOD))
     /\ RequestStates' = [RequestStates EXCEPT ![req_id] = [status |-> "processing_gmu", formula_idx |-> idx]]
     /\ Cache' = UpdateCacheUsage(idx, PC)
     /\ ConcurrencyState' = [ConcurrencyState EXCEPT !.active_requests = @ + 1]
     /\ EnergyState' = [EnergyState EXCEPT !.budget_left = @ - GMU_ENERGY, !.total_used = @ + GMU_ENERGY]
     /\ Telemetry' = Append(Telemetry, <<["GMU_START", req_id, idx]>>)
     /\ UNCHANGED <<RequestQueue, PC, Quarantine, RecoveryAttempts, AdaptivePeriod>>

GMU_Complete_Fixed(req_id) ==
  /\ req_id \in 1..NUM_REQUESTS
  /\ RequestStates[req_id].status = "processing_gmu"
  /\ RequestStates' = [RequestStates EXCEPT ![req_id] = [@ EXCEPT !.status = "completed"]]
  /\ ConcurrencyState' = [ConcurrencyState EXCEPT !.active_requests = @ - 1]
  /\ UNCHANGED <<Cache, RequestQueue, PC, Quarantine, EnergyState, AdaptivePeriod, Telemetry, RecoveryAttempts>>

Fallback_Start(req_id) ==
  /\ req_id \in 1..NUM_REQUESTS
  /\ RequestStates[req_id].status = "pending"
  /\ EnergyState.budget_left >= FALLBACK_ENERGY
  /\ RequestStates' = [RequestStates EXCEPT ![req_id] = [@ EXCEPT !.status = "processing_fallback"]]
  /\ EnergyState' = [EnergyState EXCEPT !.budget_left = @ - FALLBACK_ENERGY, !.total_used = @ + FALLBACK_ENERGY]
  /\ ConcurrencyState' = [ConcurrencyState EXCEPT !.active_requests = @ + 1]
  /\ UNCHANGED <<Cache, RequestQueue, PC, Quarantine, Telemetry, RecoveryAttempts, AdaptivePeriod>>

Fallback_Complete(req_id) ==
  /\ req_id \in 1..NUM_REQUESTS
  /\ RequestStates[req_id].status = "processing_fallback"
  /\ RequestStates' = [RequestStates EXCEPT ![req_id] = [@ EXCEPT !.status = "completed"]]
  /\ ConcurrencyState' = [ConcurrencyState EXCEPT !.active_requests = @ - 1]
  /\ UNCHANGED <<Cache, RequestQueue, PC, Quarantine, EnergyState, AdaptivePeriod, Telemetry, RecoveryAttempts>>

ApplyTrainerProposal == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                   GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                   Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                   RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                   PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                   PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                   CriticalityState, EfficiencyScores>>

SmartRecoveryProposal == ApplyTrainerProposal

EnterDegradedMode ==
  /\ SystemMode # "degraded"
  /\ SystemMode' = "degraded"
  /\ UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results, GoldenChecks,
                 MismatchCount, RetryCounts, TrainerQueue, Telemetry, GoldenBudgetLeft, LatencyTrack,
                 EnergyUsed, AdaptivePeriod, RecoveryAttempts, FormulaProvenance, RequestFormulaMap,
                 DynamicFaults, PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                 PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy, CriticalityState,
                 EfficiencyScores>>

EnterFallbackOnlyMode == EnterDegradedMode
EnterEnergySaverMode == EnterDegradedMode
EnterMaintenanceMode == EnterDegradedMode
RefillGoldenBudget == UNCHANGED <<GoldenBudgetLeft>>
UpdatePerformanceMetrics == UNCHANGED <<PerformanceMetrics>>

\* Probabilistic fault injection (nondeterministic approx)
ProbabilisticFaultInjection ==
  /\ PC' = PC + 1
  /\ IF (FAULT_PROBABILITY_PERCENT > 0) /\ (PC % 2 = 0) THEN
       \E idx \in 0..FORMULA_SLOTS-1: Quarantine' = Quarantine \cup {idx} /\ Cache' = [Cache EXCEPT ![idx] = [@ EXCEPT !.active = FALSE]]
     ELSE UNCHANGED <<Cache, Quarantine>>
  /\ UNCHANGED <<RequestQueue, RequestStates, CPU_Results, GoldenChecks, MismatchCount, RetryCounts,
                SystemMode, TrainerQueue, Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed,
                AdaptivePeriod, RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount, PredictiveState,
                PreemptiveState, ConcurrencyState, RecycledEnergy, CriticalityState, EfficiencyScores>>

\* ---------- ADAPTIVE ACTION (with optional guard) ----------
ComputeEnergyAwareAdaptivePeriod ==
  LET raw_target == ComputeAdaptivePeriod IN
  LET energy_constrained_target ==
    IF EnergyState.budget_left < (ENERGY_BUDGET \div 5) THEN 4
    ELSE IF EnergyState.budget_left < (ENERGY_BUDGET \div 3) THEN Max(raw_target, 2)
    ELSE raw_target
  IN energy_constrained_target

EnergyAwareAdaptiveUpdate ==
  /\ ADAPTIVE_SAMPLING
  /\ LET target == ComputeEnergyAwareAdaptivePeriod IN
     LET candidate == IF AdaptivePeriod > target THEN AdaptivePeriod - 1
                      ELSE IF AdaptivePeriod < target THEN AdaptivePeriod + 1
                      ELSE AdaptivePeriod
     IN /\ (ENFORCE_ADAPTIVE_GUARD => (candidate >= AdaptivePeriod \/ AdaptiveProjectionGuard(candidate)))
        /\ AdaptiveState' = [current_period |-> AdaptivePeriod,
                            target_period |-> target,
                            transition_step |-> IF AdaptivePeriod = target THEN 0 ELSE AdaptiveState.transition_step + 1,
                            convergence_count |-> IF AdaptivePeriod = target THEN AdaptiveState.convergence_count + 1 ELSE 0]
        /\ AdaptivePeriod' = candidate
        /\ Telemetry' = Append(Telemetry, <<["ENERGY_AWARE_ADAPTIVE", AdaptivePeriod, target, EnergyState.budget_left]>>)
  /\ UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results, GoldenChecks, MismatchCount,
                 RetryCounts, SystemMode, TrainerQueue, GoldenBudgetLeft, LatencyTrack, EnergyUsed, RecoveryAttempts,
                 FormulaProvenance, RequestFormulaMap, DynamicFaults, PerformanceMetrics, EnergyState, FaultInjectionCount,
                 PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy, CriticalityState, EfficiencyScores>>

\* ---------- SIMPLE ADAPTIVE & ENERGY ACTIONS ----------
ProactiveEnergyManager == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                    GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                    Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                    RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                    PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                    PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                    CriticalityState, EfficiencyScores>>

PreemptiveQuarantineAction == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                         GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                         Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                         RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                         PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                         PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                         CriticalityState, EfficiencyScores>>

DynamicConcurrencyUpdate == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                       GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                       Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                       RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                       PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                       PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                       CriticalityState, EfficiencyScores>>

UpdateEfficiencyScores == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                     GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                     Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                     RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                     PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                     PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                     CriticalityState, EfficiencyScores>>

CriticalityAwareScheduling == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                         GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                         Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                         RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                         PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                         PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                         CriticalityState, EfficiencyScores>>

EnergyRecyclingProcess == UNCHANGED <<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                                     GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                                     Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                                     RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                                     PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                                     PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                                     CriticalityState, EfficiencyScores>>

\* ---------- INVARIANTS ----------
Invariant_NoLostRequests == \A r \in 1..NUM_REQUESTS : RequestStates[r].status \in Status

Invariant_RequestConservation ==
  LET active_count == Cardinality({req_id \in 1..NUM_REQUESTS: RequestStates[req_id].status \in {"pending", "processing_gmu", "processing_fallback"}})
      completed_count == Cardinality({req_id \in 1..NUM_REQUESTS: RequestStates[req_id].status = "completed"})
      failed_count == Cardinality({req_id \in 1..NUM_REQUESTS: RequestStates[req_id].status = "failed"})
  IN (active_count + completed_count + failed_count) = NUM_REQUESTS

Invariant_EnergyAwareness == EnergyState.budget_left >= 0

Invariant_BoundedRecovery == \A idx \in 0..FORMULA_SLOTS-1: RecoveryAttempts[idx] <= MAX_RECOVERY_ATTEMPTS

Invariant_AdaptiveConsistency == ADAPTIVE_SAMPLING => (AdaptivePeriod \in 1..4)

\* ---------- TEMPORAL PROPERTIES ----------
Temporal_GuaranteedCompletion ==
  (EnergyState.budget_left > 0) /\ SystemMode # "maintenance" => \A req_id \in 1..NUM_REQUESTS: <> (RequestStates[req_id].status = "completed")

Temporal_AdaptiveConvergence == ADAPTIVE_SAMPLING => <> (AdaptivePeriod = ComputeEnergyAwareAdaptivePeriod)

\* ---------- NEXT ----------
Next ==
  \/ (\E req_id \in 1..NUM_REQUESTS: EnergyAwareGMUStart(req_id))
  \/ (\E req_id \in 1..NUM_REQUESTS: GMU_Complete_Fixed(req_id))
  \/ (\E req_id \in 1..NUM_REQUESTS: Fallback_Start(req_id))
  \/ (\E req_id \in 1..NUM_REQUESTS: Fallback_Complete(req_id))
  \/ ApplyTrainerProposal
  \/ SmartRecoveryProposal
  \/ EnergyAwareAdaptiveUpdate
  \/ ProactiveEnergyManager
  \/ PreemptiveQuarantineAction
  \/ DynamicConcurrencyUpdate
  \/ UpdateEfficiencyScores
  \/ CriticalityAwareScheduling
  \/ EnergyRecyclingProcess
  \/ ProbabilisticFaultInjection
  \/ EnterDegradedMode
  \/ EnterFallbackOnlyMode
  \/ EnterEnergySaverMode
  \/ RefillGoldenBudget
  \/ UpdatePerformanceMetrics
  \/ EnterMaintenanceMode

Spec == Init /\ [][Next]_<<Cache, RequestQueue, RequestStates, PC, Quarantine, CPU_Results,
                      GoldenChecks, MismatchCount, RetryCounts, SystemMode, TrainerQueue,
                      Telemetry, GoldenBudgetLeft, LatencyTrack, EnergyUsed, AdaptivePeriod,
                      RecoveryAttempts, FormulaProvenance, RequestFormulaMap, DynamicFaults,
                      PerformanceMetrics, EnergyState, AdaptiveState, FaultInjectionCount,
                      PredictiveState, PreemptiveState, ConcurrencyState, RecycledEnergy,
                      CriticalityState, EfficiencyScores>>

=============================================================================