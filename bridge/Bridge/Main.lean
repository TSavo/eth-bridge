/-
The bridge: OpenAI's formal claim (`Bridge.OpenAIStatement`, their comparator statement verbatim as a
proposition) implies Anthropic's formal `MainResults.ETHIsFalse`. The route reuses Anthropic's machine
layer: a `Groundwork.Stepped` computation with `IsPolyT` init/step/out compiles to one of Mathlib's
FinTM2 machines by `Groundwork.exists_tm`, with polynomial overhead per step; a machine that decides
3-SAT within c·2^{δn} steps for every δ gives `Sat3.SubexpTM`, and `WidthThree.ethFails_of_subexpTM`
turns that into `¬ Sat3.ETH_TM`, which is `MainResults.ETHIsFalse` by unfolding.

Each `sorry` below is one of the four lemmas named in the plan: (1) analysis, (2) encoding length,
(3) the front end, (4) OpenAI's primitive machine as a stepped computation with polynomial-time
init/step/out and states bounded by its visited space.
-/
import MainResults
import ThreeSatRateStatement
import WidthThree.Rates
import ToTuring.Machine.Host
import ToTuring.Closure.Basic
import ToTuring.Closure.Cases
import ToTuring.Closure.Fold
import ToTuring.Lib.Bool
import ToTuring.Lib.Nat1
import ToTuring.Lib.Nat1b
import ToTuring.Lib.Nat2
import ToTuring.Lib.Int
import ToTuring.Lib.List1
import ToTuring.Lib.List1b
import ToTuring.Lib.List2
import ToTuring.Lib.List3
import ToTuring.Lib.Table
import ToTuring.Lib.Unary
import Bridge.OpenAIStatement

open OAI.Algorithms.SubexponentialSAT Turing Groundwork
open scoped NNReal

namespace Bridge


/-! ## 0. The target, and the step that is already theirs -/

/-- `¬ Sat3.ETH_TM` is `MainResults.ETHIsFalse` by unfolding (the same check `Solution.lean` relies on). -/
theorem ethIsFalse_of_subexpTM (h : Sat3.SubexpTM) : MainResults.ETHIsFalse :=
  WidthThree.ethFails_of_subexpTM h

/-! ## 1. Analysis: OpenAI's exponent is o(n). -/

/-- `runtimeScale n = n (ln ln (n+16))² / √(ln (n+16))` is eventually below `δ n` for every δ > 0. -/
theorem runtimeScale_sublinear (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SqrtLog.Statement.runtimeScale n ≤ δ * n := by
  -- (log y)² / √y → 0 as y → ∞, since log = o(y^{1/4}).
  have hlo : (fun y : ℝ => Real.log y ^ 2) =o[Filter.atTop] (fun y : ℝ => Real.sqrt y) := by
    have h := isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)
    refine h.congr' ?_ ?_
    · filter_upwards with y; exact Real.rpow_two _
    · filter_upwards with y; exact (Real.sqrt_eq_rpow y).symm
  have h1 : Filter.Tendsto (fun y : ℝ => Real.log y ^ 2 / Real.sqrt y) Filter.atTop (nhds 0) :=
    hlo.tendsto_div_nhds_zero
  -- log (n + 16) → ∞.
  have h2 : Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 16)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h3 := (h1.comp h2).eventually (gt_mem_nhds hδ)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h3
  refine ⟨N, fun n hn => ?_⟩
  have hlt : Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16)) < δ := hN n hn
  unfold SqrtLog.Statement.runtimeScale
  rw [mul_div_assoc, mul_comm δ]
  exact mul_le_mul_of_nonneg_left hlt.le (Nat.cast_nonneg n)

/-! ## 2. The OpenAI input word has length polynomial in n for width-k formulas. -/

theorem formulaBitLength_poly (k : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
      Encoding.formulaBitLength F ≤ c * (n + 1) ^ (k + 2) := by
  sorry

/-! ## 3. The front end: Anthropic's plain code ↦ OpenAI's canonical code. -/

/-- Anthropic's list-of-lists CNF as OpenAI's Finset-of-Finsets CNF. -/
def toFinsetCNF {n : ℕ} (φ : Sat3.CNF n) : SAT.CNF (Fin n) :=
  (φ.map fun C => (C.map fun l => (⟨l.1, l.2⟩ : SAT.Literal (Fin n))).toFinset).toFinset

theorem toFinsetCNF_width {n : ℕ} (φ : Sat3.CNF n) (h : Sat3.Is3CNF φ) :
    SAT.WidthAtMost 3 (toFinsetCNF φ) := by
  intro C' hC'
  unfold toFinsetCNF at hC'
  rw [List.mem_toFinset, List.mem_map] at hC'
  obtain ⟨C, hC, rfl⟩ := hC'
  calc (C.map fun l => (⟨l.1, l.2⟩ : SAT.Literal (Fin n))).toFinset.card
      ≤ (C.map fun l => (⟨l.1, l.2⟩ : SAT.Literal (Fin n))).length := List.toFinset_card_le _
    _ = C.length := by simp
    _ ≤ 3 := h.1 C hC

theorem eval_toFinsetCNF_iff {n : ℕ} (φ : Sat3.CNF n) (a : Fin n → Bool) :
    (toFinsetCNF φ).eval a = true ↔ ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2 := by
  rw [SAT.CNF.eval, decide_eq_true_iff]
  simp only [SAT.Clause.eval, decide_eq_true_iff, SAT.Literal.eval, beq_iff_eq, toFinsetCNF,
    List.mem_toFinset, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h C hC
    obtain ⟨_, ⟨l, hl, rfl⟩, e⟩ := h C hC
    exact ⟨l, hl, e⟩
  · intro h C hC
    obtain ⟨l, hl, e⟩ := h C hC
    exact ⟨_, ⟨l, hl, rfl⟩, e⟩

theorem satisfiable_iff_count_pos {n : ℕ} (φ : Sat3.CNF n) :
    Sat3.Satisfiable φ ↔ 0 < SAT.count (toFinsetCNF φ) := by
  unfold SAT.count SAT.satisfyingAssignments Sat3.Satisfiable
  rw [Finset.card_pos, Finset.filter_nonempty_iff]
  simp only [Finset.mem_univ, true_and, eval_toFinsetCNF_iff]

/-- A polynomial-time `pre` that maps every plain code of a 3-CNF to OpenAI's code of the same formula. -/
theorem frontEnd_exists : ∃ pre : List Bool → List Bool, PolyT pre ∧
    ∀ (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → pre (Sat3.enc φ) = Encoding.encodeCNF (toFinsetCNF φ) := by
  sorry

/-! ## 4. OpenAI's primitive machine as a stepped computation.

A tape is kept as (cells left of the head, reversed; the head cell; cells to the right), trimmed, so
that its size is bounded by the span of visited cells. The machine state `Bool ⊕ Fin stateCount` is
kept as `Bool ⊕ ℕ`. All of these types have `Enc` and `HasSize` instances in Anthropic's layer. -/

abbrev TapeRep : Type := List (Option Bool) × Option Bool × List (Option Bool)

/-- The configuration representation of a primitive machine: state and one tape per index. -/
abbrev CfgRep : Type := (Bool ⊕ ℕ) × List TapeRep

/-- The tape a representation stands for. -/
def TapeRep.toTape (r : TapeRep) : Tape (Option Bool) :=
  Tape.mk' (ListBlank.mk r.1) (ListBlank.mk (r.2.1 :: r.2.2))

/-- The configuration a representation stands for, when its state index and tape count are in range. -/
def toCfg (P : Computation.PrimitiveMachine) (r : CfgRep) : Option P.Cfg :=
  if h : r.2.length = P.tapeCount then
    match r.1 with
    | .inl b => some ⟨.inl b, fun i => (r.2[i.val]'(by rw [h]; exact i.isLt)).toTape⟩
    | .inr q => if hq : q < P.stateCount then
        some ⟨.inr ⟨q, hq⟩, fun i => (r.2[i.val]'(by rw [h]; exact i.isLt)).toTape⟩ else none
  else none

/-- An action: `.inl false` = move left, `.inl true` = move right, `.inr b` = write `b`. -/
abbrev Act : Type := Bool ⊕ Option Bool

/-- A transition result: halt with a bit, or (next state index, action). -/
abbrev Trans : Type := Bool ⊕ (ℕ × Act)

def actOf : Turing.TM0.Stmt (Option Bool) → Act
  | .move .left => .inl false
  | .move .right => .inl true
  | .write b => .inr b

def transOf {P : Computation.PrimitiveMachine} :
    Bool ⊕ (Fin P.stateCount × Turing.TM0.Stmt (Option Bool)) → Trans
  | .inl b => .inl b
  | .inr (q, a) => .inr (q.val, actOf a)

/-- The index of a cell symbol: blank 0, `false` 1, `true` 2. -/
def symIdx (c : Option Bool) : ℕ := c.elim 0 fun b => bif b then 2 else 1

/-- The transition table of `P` as data: row `q`, column `symIdx c`. -/
def table (P : Computation.PrimitiveMachine) : List (List Trans) :=
  (List.finRange P.stateCount).map fun q =>
    [none, some false, some true].map fun c => transOf (P.transition q c)

/-- The scanned tape of each state, as data. -/
def scanTable (P : Computation.PrimitiveMachine) : List ℕ :=
  (List.finRange P.stateCount).map fun q => (P.scan q).val

/-- Head moves and writes on a representation, in combinator form. Leaving the represented span
appends one blank cell, so the representation grows exactly when the run visits a new cell. -/
def moveL (t : TapeRep) : TapeRep := (t.1.tail, t.1.headD none, t.2.1 :: t.2.2)
def moveR (t : TapeRep) : TapeRep := (t.2.1 :: t.1, t.2.2.headD none, t.2.2.tail)
def writeC (b : Option Bool) (t : TapeRep) : TapeRep := (t.1, b, t.2.2)
def applyAct (a : Act) (t : TapeRep) : TapeRep :=
  a.elim (fun d => bif d then moveR t else moveL t) fun b => writeC b t

/-- `List.set` written with `take`/`drop`. -/
def setAt (l : List TapeRep) (i : ℕ) (t : TapeRep) : List TapeRep := l.take i ++ t :: l.drop (i + 1)

theorem default_optionBool : (default : Option Bool) = none := rfl

/-- A trailing blank cell does not change a `ListBlank`. -/
theorem ListBlank.mk_singleton_none : ListBlank.mk ([none] : List (Option Bool)) = ListBlank.mk [] :=
  Quotient.sound (Or.inr ⟨1, rfl⟩)

theorem toTape_moveL (t : TapeRep) : (moveL t).toTape = t.toTape.move .left := by
  obtain ⟨L, h, R⟩ := t
  cases L <;>
    simp [moveL, TapeRep.toTape, Tape.move_left_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk, default_optionBool]

theorem toTape_moveR (t : TapeRep) : (moveR t).toTape = t.toTape.move .right := by
  obtain ⟨L, h, R⟩ := t
  cases R <;>
    simp [moveR, TapeRep.toTape, Tape.move_right_mk', ListBlank.head_mk, ListBlank.tail_mk,
      ListBlank.cons_mk, default_optionBool, ListBlank.mk_singleton_none]

theorem toTape_writeC (b : Option Bool) (t : TapeRep) : (writeC b t).toTape = t.toTape.write b := by
  obtain ⟨L, h, R⟩ := t
  simp [writeC, TapeRep.toTape, Tape.write_mk', ListBlank.tail_mk, ListBlank.cons_mk]

/-- One step on the representation: look up the scanned tape and the transition in the tables; a
halted state is a fixed point; an out-of-range state halts with `false` (never reached from `toCfg`). -/
def stepRep (P : Computation.PrimitiveMachine) (r : CfgRep) : CfgRep :=
  r.1.elim (fun _ => r) fun q =>
    (((table P).getD q []).getD (symIdx (r.2.getD ((scanTable P).getD q 0) ([], none, [])).2.1)
        (.inl false)).elim
      (fun ans => (.inl ans, r.2))
      fun p => (.inr p.1, setAt r.2 ((scanTable P).getD q 0)
        (applyAct p.2 (r.2.getD ((scanTable P).getD q 0) ([], none, []))))

theorem stepRep_polyT (P : Computation.PrimitiveMachine) : PolyT (stepRep P) := by
  unfold stepRep setAt applyAct writeC moveL moveR symIdx
  fun_prop

/-- The input representation: the word on the input tape, head on its first cell, other tapes blank. -/
def initRep (P : Computation.PrimitiveMachine) (x : List Bool) : CfgRep :=
  (.inr P.start.val,
    List.replicate P.inputTape.val ([], none, []) ++
      ([], x.head?, (x.drop 1).map some) :: List.replicate (P.tapeCount - P.inputTape.val - 1) ([], none, []))

/-- The output: the halting bit, once halted. -/
def outRep (r : CfgRep) : Option Bool := r.1.elim (fun b => some b) fun _ => none

/-- OpenAI's machine behind the front end `pre`, as a stepped computation on bit strings. -/
def stepped (P : Computation.PrimitiveMachine) (pre : List Bool → List Bool) : Stepped (List Bool) Bool where
  σ := CfgRep
  init x := initRep P (pre x)
  step := stepRep P
  out := outRep

theorem stepRep_sound (P : Computation.PrimitiveMachine) (r : CfgRep) (c : P.Cfg) (h : toCfg P r = some c) :
    (toCfg P (stepRep P r)) = (P.step c).elim (toCfg P r) some := by
  sorry

instance carried_cfgRep : Carried CfgRep := inferInstance

/-- `IsPolyT` for OpenAI's machine behind a polynomial-time front end. A `def`, not an instance, because
it takes the proof `hpre`; `subexpTM_of_claimAt3` installs it with `haveI`. -/
def isPolyT_stepped (P : Computation.PrimitiveMachine) (pre : List Bool → List Bool) (hpre : PolyT pre) :
    IsPolyT (stepped P pre) where
  enc := inferInstanceAs (Enc CfgRep)
  carried := carried_cfgRep
  init := by
    show PolyT fun x => initRep P (pre x)
    unfold initRep
    fun_prop
  step := stepRep_polyT P
  out := by
    show PolyT outRep
    unfold outRep
    fun_prop

/-- The size of a reachable representation is bounded by the visited space of the run. -/
theorem size_le_visitedSpace (P : Computation.PrimitiveMachine) (x : List Bool) (t : ℕ)
    (final : SqrtLogSpace.LocatedCfg P)
    (h : Computation.Trace (SqrtLogSpace.locatedStep P) t (SqrtLogSpace.locatedInit P x) final) :
    size ((stepRep P)^[t] (initRep P x)) ≤ 3 * SqrtLogSpace.visitedSpace final + 3 * P.tapeCount + 4 := by
  sorry

/-! ## 5. Assembly. -/

/-- From `ClaimAt 3`: one FinTM2 decides 3-SAT within A·2^{δn} steps for every δ > 0. -/
theorem subexpTM_of_claimAt3 (h : SqrtLogSpace.ClaimAt 3) : Sat3.SubexpTM := by
  sorry

/-- **The bridge.** OpenAI's claim implies Anthropic's `ETHIsFalse`. -/
theorem ethIsFalse_of_claim (h : SqrtLogSpace.Claim) : MainResults.ETHIsFalse :=
  ethIsFalse_of_subexpTM (subexpTM_of_claimAt3 (h 3 (by norm_num)))

end Bridge
