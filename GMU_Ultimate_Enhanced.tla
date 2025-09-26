------------------------------- MODULE GMU_Ultimate_Enhanced -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    FORMULAS, CPUS, MAX_RETRIES, SAMPLE_PERIOD,
    LATENCY_GMU, LATENCY_FALLBACK, GOLDEN_BUDGET, EPOCH_LENGTH

VARIABLES
    ActiveCache, LRU, Quarantine, TrainerQueue, Telemetry,
    ReqQ, Inflight, Completed, GoldenBudgetLeft, SystemMode, PC, LatencyTrack

Req(cpu, fml, retry, id) == [cpu |-> cpu, formula |-> fml, retries |-> retry, id |-> id]
NoneReq == [cpu |-> -1, formula |-> -1, retries |-> 0, id |-> -1]

Init ==
    /\ ActiveCache = [i \in 1..5 |-> CHOOSE f \in FORMULAS: TRUE]
    /\ LRU = <<1,2,3,4,5>>
    /\ Quarantine = {}
    /\ TrainerQueue = <<>>
    /\ Telemetry = <<>>
    /\ ReqQ = <<>>
    /\ Inflight = [c \in CPUS |-> NoneReq]
    /\ Completed = <<>>
    /\ GoldenBudgetLeft = GOLDEN_BUDGET
    /\ SystemMode = "normal"
    /\ PC = 0
    /\ LatencyTrack = [id \in Nat |-> 0]

IsQuarantined(idx) == idx \in Quarantine

IssueRequest(c, fml, id) ==
    /\ Inflight[c] = NoneReq
    /\ Inflight' = [Inflight EXCEPT ![c] = Req(c, fml, 0, id)]
    /\ UNCHANGED <<ActiveCache, LRU, Quarantine, TrainerQueue, Telemetry, ReqQ, Completed, GoldenBudgetLeft, SystemMode, PC, LatencyTrack>>

GMUFast(c) ==
    LET r == Inflight[c] IN
    /\ r # NoneReq
    /\ ~IsQuarantined(CHOOSE idx \in DOMAIN ActiveCache: ActiveCache[idx] = r.formula)
    /\ GoldenBudgetLeft > 0
    /\ Completed' = Append(Completed, r)
    /\ Inflight' = [Inflight EXCEPT ![c] = NoneReq]
    /\ Telemetry' = Append(Telemetry, << "GMU_PASS", r.id >>)
    /\ GoldenBudgetLeft' = GoldenBudgetLeft - 1
    /\ LatencyTrack' = [LatencyTrack EXCEPT ![r.id] = @ + LATENCY_GMU]
    /\ UNCHANGED <<ActiveCache, LRU, Quarantine, TrainerQueue, ReqQ, SystemMode, PC>>

Fallback(c) ==
    LET r == Inflight[c] IN
    /\ r # NoneReq
    /\ Completed' = Append(Completed, r)
    /\ Inflight' = [Inflight EXCEPT ![c] = NoneReq]
    /\ Telemetry' = Append(Telemetry, << "FALLBACK", r.id >>)
    /\ LatencyTrack' = [LatencyTrack EXCEPT ![r.id] = @ + LATENCY_FALLBACK]
    /\ UNCHANGED <<ActiveCache, LRU, Quarantine, TrainerQueue, ReqQ, GoldenBudgetLeft, SystemMode, PC>>

ProposeFormula(fml) ==
    /\ TrainerQueue' = Append(TrainerQueue, fml)
    /\ Telemetry' = Append(Telemetry, << "TRAINER_PROPOSE", fml >>)
    /\ UNCHANGED <<ActiveCache, LRU, Quarantine, Inflight, ReqQ, Completed, GoldenBudgetLeft, SystemMode, PC, LatencyTrack>>

ApplyTrainerProposal ==
    /\ TrainerQueue # <<>>
    /\ LET fml == Head(TrainerQueue) IN
       ActiveCache' = [ActiveCache EXCEPT ![CHOOSE i \in DOMAIN ActiveCache: TRUE] = fml]
    /\ TrainerQueue' = Tail(TrainerQueue)
    /\ Telemetry' = Append(Telemetry, << "TRAINER_APPLY", fml >>)
    /\ UNCHANGED <<LRU, Quarantine, Inflight, ReqQ, Completed, GoldenBudgetLeft, SystemMode, PC, LatencyTrack>>

RefillBudget ==
    IF PC % EPOCH_LENGTH = 0 THEN GoldenBudgetLeft' = GOLDEN_BUDGET ELSE GoldenBudgetLeft' = GoldenBudgetLeft
    /\ UNCHANGED <<ActiveCache, LRU, Quarantine, TrainerQueue, Telemetry, ReqQ, Inflight, Completed, SystemMode, PC, LatencyTrack>>

Next ==
    \/ \E c \in CPUS: IssueRequest(c, CHOOSE f \in FORMULAS: TRUE, PC)
    \/ \E c \in CPUS: GMUFast(c)
    \/ \E c \in CPUS: Fallback(c)
    \/ \E f \in FORMULAS: ProposeFormula(f)
    \/ ApplyTrainerProposal
    \/ RefillBudget

Spec == Init /\ [][Next]_<<ActiveCache,LRU,Quarantine,TrainerQueue,Telemetry,ReqQ,Inflight,Completed,GoldenBudgetLeft,SystemMode,PC,LatencyTrack>>

NoUseOfQuarantined ==
    \A c \in CPUS: ~(\E idx \in Quarantine: ActiveCache[idx] = Inflight[c].formula)

GoldenBudgetNonNegative == GoldenBudgetLeft >= 0

EventuallyQuarantine == WF_<<ActiveCache,LRU,Quarantine,TrainerQueue,Telemetry,ReqQ,Inflight,Completed,GoldenBudgetLeft,SystemMode,PC,LatencyTrack>>(\E c \in CPUS: GMUFast(c))

ReqCompletes == []<>(\E r \in Completed: TRUE)

SafeTelemetry == \A ev \in Telemetry: ev # <<>>
================================================================================
