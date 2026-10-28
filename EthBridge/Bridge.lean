/-
The bridge: OpenAI's formal claim (a primitive multi-tape machine counts k-CNF assignments within
C·(L+1)^d·2^(A·runtimeScale n) steps) implies Anthropic's formal `MainResults.ETHIsFalse` (s₃ = 0 on
Mathlib's FinTM2 machines). Both trusted statement files are included verbatim in this project; this
file adds only the theorem that connects them, decomposed into the four lemmas its proof needs.
-/
import EthBridge.MainResults
import EthBridge.SubexponentialSAT

open OAI.Algorithms.SubexponentialSAT
open scoped NNReal

namespace EthBridge

/-! ### Lemma 1: the exponent is o(n). -/

/-- `runtimeScale n = n (ln ln (n+16))² / √(ln (n+16))` is eventually below `δ n` for every δ > 0. -/
theorem runtimeScale_sublinear (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → SqrtLog.Statement.runtimeScale n ≤ δ * n := by
  sorry

/-! ### Lemma 2: the OpenAI encoding has length polynomial in n for width-k formulas. -/

/-- A width-`k` CNF on `Fin n` has at most `(2n+1)^k` clauses and each clause encodes in `O(k n)` bits
(literal codes are unary), so `formulaBitLength F ≤ c (n+1)^(k+2)` for a constant `c = c k`. -/
theorem formulaBitLength_poly (k : ℕ) :
    ∃ c : ℕ, ∀ (n : ℕ) (F : SAT.CNF (Fin n)), SAT.WidthAtMost k F →
      Encoding.formulaBitLength F ≤ c * (n + 1) ^ (k + 2) := by
  sorry

/-! ### Lemma 3: Anthropic's input word translates to OpenAI's in polynomial time.

Anthropic's `MainResults.encClauses k φ` is a list-of-lists CNF (`List (List (Fin n × Bool))`, clauses
`Nodup`, width ≤ k); OpenAI's `Encoding.encodeCNF F` is a `Finset (Finset (Literal (Fin n)))`. The
translation is: literal `(i, b)` ↦ `⟨i, b⟩`, clause list ↦ its Finset, formula list ↦ its Finset. It
preserves satisfiability and the satisfying-assignment count, and is computable by a FinTM2 in time
polynomial in the input length. We state only what the bridge needs. -/

/-- Translate Anthropic's CNF to OpenAI's. -/
def toFinsetCNF {n : ℕ} (φ : MainResults.CNF n) : SAT.CNF (Fin n) :=
  (φ.map fun C => (C.map fun l => (⟨l.1, l.2⟩ : SAT.Literal (Fin n))).toFinset).toFinset

theorem toFinsetCNF_width {k n : ℕ} (φ : MainResults.CNF n) (h : MainResults.IsKCNF k φ) :
    SAT.WidthAtMost k (toFinsetCNF φ) := by
  sorry

theorem toFinsetCNF_satisfiable {n : ℕ} (φ : MainResults.CNF n) :
    MainResults.Satisfiable φ ↔ 0 < SAT.count (toFinsetCNF φ) := by
  sorry

/-! ### Lemma 4: a `PrimitiveMachine` run is simulated by a `FinTM2` with polynomial overhead.

This is the real content: a multi-tape Turing machine with one tape operation per step is simulated by
Mathlib's multi-stack machine (two stacks per tape), with a constant number of stack operations per
tape step, plus input re-encoding (`MainResults.encClauses 3 φ` ↦ `Encoding.encodeCNF (toFinsetCNF φ)`)
and output extraction (`answerTape` cell ↦ one output bit). -/

theorem simulate_primitive_machine (k : ℕ) (hk : 2 ≤ k) (h : ClaimAt k) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (c d : ℕ) (A : ℝ),
      (∀ i, Finite (M.tm.Γ i)) ∧ 0 < A ∧
      ∀ (n : ℕ) (φ : MainResults.CNF n), MainResults.IsKCNF k φ →
        ∃ b : Bool, (b = true ↔ MainResults.Satisfiable φ) ∧
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((MainResults.encClauses k φ).map M.inputAlphabet.invFun)
            (some ([b].map M.outputAlphabet.invFun))
            ⌊(c : ℝ) * ((n : ℝ) + 1) ^ d * (2 : ℝ) ^ (A * SqrtLog.Statement.runtimeScale n)⌋₊) := by
  sorry

/-! ### The bridge. -/

/-- From Lemma 4 at k = 3 and Lemma 1: for every δ > 0 some FinTM2 decides 3-SAT within
`c'·2^{δ n}` steps, i.e. `MainResults.InTime 3 δ`; hence `s 3 = 0`, i.e. `¬ MainResults.ETH`. -/
theorem openai_claim_implies_eth_false (h : Claim) : MainResults.ETHIsFalse := by
  sorry

end EthBridge
