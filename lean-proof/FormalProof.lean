import Mathlib

/-!
# Formal proof: falsifying the completeness of a single fixed-memory component
  on open inversion tasks
  (Lean 4 + Mathlib; accompanies the paper "Formal Falsification of the
  Completeness of a Single Fixed-Memory Component for Open Inversion Tasks")

**Integrity statement (Route A)**
This file formalizes the paper's algebraic skeleton, fully implemented with zero
`sorry`. Every measure-theoretic premise not made explicit in the paper's prose
(tail realization, positive risk gap, non-negative minimum risk) is included
explicitly as a **hypothesis parameter of the theorem**, never assumed
implicitly; "positive risk gap" is additionally substantiated by the
two-sided toy: `modeB_positive_gap` bounds every frozen rule's total loss below
by 1, while `modeA_loss_lower_bound` and `modeA_loss_attained` show the best
evidence-only rule attains exactly 1/2, so the class gap is a positive 1/2.
A second, evidence-computable variant (`evidenceTarget`, `modeB_evidence_gap`,
`modeA_evidence_attained`, `evidence_gap_is_full`) replaces the demand by one
computable from evidence alone, the case Assumption A0 asks for: a constructive
evidence-instantiated rule then attains the optimal risk 0, so the whole frozen
loss of 3/2 on the same sample is gap.

Core components:
  Definition 1 (ill-posedness: the observation mask has holes, with the
  bidirectional criteria `illPosed_of_hole` and `not_illPosed_of_full`),
  Definition 2 (Modes A/B), Definition 3 (Paradigms E/I),
  Definition 4 (inference-time frozen parameters of a pure SPN).
  Lemma 1 (a single λ at an arbitrary fitting point forces data residuals and
  consistency terms to be proportional across locations).
  Lemma 2 (Paradigm E has no nonzero stationary point under heterogeneity;
  the Paradigm I objective always has a unique minimizer).
  Lemma 3 (measure premises made explicit, plus toy instantiation).
  Proposition 4 (the network rule is Mode B and not Mode A),
  Proposition 6 (same for a pure SPN).
  Theorems 5 and 7 (collision sample pair from criterion P3 ⇒ not Mode A).
  `finale`: the conjunctive composition of Lemma 3 and Theorem 5, joining the
  generalization side and the carrier side.
  Section 8.8: the generalization layer from the toy carrier to the continuous
  setting (domain-free algebraic cores and structured general forms).
-/

namespace FormalProof

/-! ## 1. Basic notation -/

abbrev Pixel := Fin 4
abbrev Depth := Pixel → ℝ

/-! ## 2. Definition 1: ill-posedness (observation mask) -/

/-- Observation: pixels inside the mask carry values; pixels outside are
unobserved. -/
structure Observation where
  mask : Pixel → Bool
  value : Pixel → ℝ

/-- Definition 1 (ill-posedness): one observation is compatible with two
different structure fields. Both candidate fields must agree with the
observation on the mask, so the definition is non-vacuous: it is provable when
the observation has holes (`illPosed_of_hole`) and refutable under a full mask
(`not_illPosed_of_full`). -/
def IllPosed (obs : Observation) : Prop :=
  ∃ ξ1 ξ2 : Depth, ξ1 ≠ ξ2 ∧
    ∀ i : Pixel, obs.mask i = true → ξ1 i = obs.value i ∧ ξ2 i = obs.value i

/-- Hole ⇒ ill-posed: on pixels outside the mask, two observation-compatible
structure fields may fork freely. -/
theorem illPosed_of_hole {obs : Observation} {j : Pixel} (hj : obs.mask j = false) :
    IllPosed obs := by
  refine ⟨fun i => if i = j then (0 : ℝ) else obs.value i,
          fun i => if i = j then (1 : ℝ) else obs.value i, ?_, ?_⟩
  · intro h
    have h0 := congrFun h j
    simp at h0
  · intro i hi
    have hij : ¬ i = j := by
      intro h
      subst h
      rw [hj] at hi
      exact Bool.noConfusion hi
    exact ⟨by simp [hij], by simp [hij]⟩

/-- Full mask ⇒ not ill-posed: when the observation pins down every pixel, the
structure field is uniquely determined. -/
theorem not_illPosed_of_full {obs : Observation} (hf : ∀ i, obs.mask i = true) :
    ¬ IllPosed obs := by
  rintro ⟨ξ1, ξ2, hne, hfit⟩
  apply hne
  funext i
  obtain ⟨h1, h2⟩ := hfit i (hf i)
  rw [h1, h2]

/-! ## 3. Definition 2: context rules and Modes A / B -/

abbrev ContextRule := Depth → ℝ

/-- Mode A (dependence criterion): there exists Φ such that the rule value
depends only on the evidence pixel.
Note: the essence of Definition 3 in the paper is the provenance criterion,
where values are instantiated by current evidence or analytic invariants. The
dependence criterion is the decidable projection of the provenance criterion
onto the toy carrier: the evidence-only functional form is the only decidable
form of provenance on the toy carrier. Classification concerns the provenance
of the function, not its carrier: frozen parameters implementing an analytic
invariant still count as Mode A; frozen parameters implementing a
corpus-statistical function still count as Mode B. -/
def IsModeA (R : ContextRule) : Prop :=
  ∃ Φ : (ℝ → ℝ), ∀ d : Depth, R d = Φ (d 0)

/-- Mode B: the rule is computed from a fixed parameter W (the parameter is
fixed; the value may vary with the input). -/
def IsModeB (W : ℝ) (R : ContextRule) : Prop :=
  ∀ d : Depth, R d = W * (d 0 - d 1)

/-! ## 4. Definition 3: objective paradigms E / I -/

def DataTerm (x d : Depth) (i : Pixel) : ℝ := (x i - d i)^2

/-- Paradigm E: an additively separable objective with a penalty term appended
to the data term. Its first-order condition in d_i is `ParadigmEFirstOrder`
(constant factors normalized). -/
def ParadigmE (x d : Depth) (lambda : ℝ) : ℝ :=
  ∑ i : Pixel, DataTerm x d i +
    lambda * ∑ i : Pixel, ∑ j : Pixel, (d i - d j)^2

def ParadigmI (x pred : Depth) : ℝ :=
  ∑ i : Pixel, (x i - pred i)^2

/-! ## 5. Lemma 1: a global scalar cannot accommodate heterogeneous
consistency terms -/

def kappa (d : Depth) (i : Pixel) : ℝ := ∑ j : Pixel, (d i - d j)

abbrev IsBoundary (i : Pixel) : Prop := i = 0
abbrev IsInterior (i : Pixel) : Prop := i ≠ 0

/-- First-order condition (Paradigm E in d_i):
$\partial\ell_i/\partial d_i + \lambda \kappa_i(d)=0$. -/
def FirstOrder (x d : Depth) (lambda : ℝ) (i : Pixel) : Prop :=
  (d i - x i) + lambda * kappa d i = 0

/-- Lemma 1 (strengthened form): if a single global scalar satisfies both
first-order conditions at an arbitrary fitting point, then data residuals and
consistency terms must be proportional across locations; when this
proportionality fails, contradiction. Covers arbitrary fitting points, not
only the zero-residual manifold. -/
theorem lemma1_sharp {x d : Depth} {lambda : ℝ} {i j : Pixel}
    (h1 : FirstOrder x d lambda i) (h2 : FirstOrder x d lambda j)
    (hHetero : (x i - d i) * kappa d j ≠ (x j - d j) * kappa d i) :
    False := by
  unfold FirstOrder at h1 h2
  have e1 : lambda * kappa d i = x i - d i := by linarith
  have e2 : lambda * kappa d j = x j - d j := by linarith
  apply hHetero
  calc (x i - d i) * kappa d j = lambda * kappa d i * kappa d j := by rw [← e1]
    _ = lambda * kappa d j * kappa d i := by ring
    _ = (x j - d j) * kappa d i := by rw [← e2]

/-- Lemma 1 (zero-residual specialization): nonzero λ and heterogeneous
consistency terms ⇒ no constant λ satisfies the first-order conditions. -/
theorem lemma1_final
  {d : Depth} {i j : Pixel}
  (hHetero : kappa d i ≠ kappa d j) :
  ¬ ∃ lambda : ℝ, lambda ≠ 0 ∧
    FirstOrder d d lambda i ∧ FirstOrder d d lambda j := by
  intro hlambda
  rcases hlambda with ⟨lambda, hlambdanz, h1, h2⟩
  unfold FirstOrder at h1 h2
  have hI : lambda * kappa d i = 0 := by linarith
  have hJ : lambda * kappa d j = 0 := by linarith
  have hij : kappa d i = kappa d j := by
    apply mul_left_cancel₀ hlambdanz
    calc
      lambda * kappa d i = 0 := hI
      _ = lambda * kappa d j := by rw [← hJ]
  exact hHetero hij

/-! ## 5.5 Lemma 2: Paradigm E infeasible, Paradigm I uniquely optimal -/

/-- First-order stationarity condition of Paradigm E at (d, λ)
(zero-residual form). -/
def ParadigmEFirstOrder (d : Depth) (lambda : ℝ) (i : Pixel) : Prop :=
  (d i - d i) + lambda * kappa d i = 0

/-- Lemma 2 (E side): if the consistency terms are heterogeneous (κ_i≠κ_j),
no λ≠0 satisfies the two first-order conditions of Paradigm E. -/
theorem lemma2_E_stationary_infeasible
  {d : Depth} {i j : Pixel}
  (hHetero : kappa d i ≠ kappa d j) :
  ¬ ∃ lambda : ℝ, lambda ≠ 0 ∧
    ParadigmEFirstOrder d lambda i ∧ ParadigmEFirstOrder d lambda j := by
  intro hlam
  rcases hlam with ⟨lambda, hlamnz, h1, h2⟩
  unfold ParadigmEFirstOrder at h1 h2
  have hI : lambda * kappa d i = 0 := by linarith
  have hJ : lambda * kappa d j = 0 := by linarith
  have hij : kappa d i = kappa d j := by
    apply mul_left_cancel₀ hlamnz
    calc
      lambda * kappa d i = 0 := hI
      _ = lambda * kappa d j := by rw [← hJ]
  exact hHetero hij

/-- Paradigm I predicate: a single generative term with no separate additive
regularizer (Paradigm I of Definition 3). -/
def IsParadigmI (pred : Depth → ℝ) : Prop :=
  ∃ p : Depth, ∀ x : Depth, pred x = ∑ i : Pixel, (x i - p i)^2

/-- The Paradigm I objective always has a unique minimizer: minimality follows
from non-negativity of the squared sum, uniqueness from termwise vanishing of
a zero squared sum. -/
theorem paradigmI_unique_minimizer {pred : Depth → ℝ} (h : IsParadigmI pred) :
    ∃ p : Depth, (∀ y, pred p ≤ pred y) ∧ (∀ y, pred y = pred p → y = p) := by
  rcases h with ⟨p, hp⟩
  have hp0 : pred p = 0 := by
    rw [hp]
    apply Finset.sum_eq_zero
    intro i _
    simp
  refine ⟨p, fun y => ?_, fun y hy => ?_⟩
  · rw [hp0, hp]
    apply Finset.sum_nonneg
    intro i _
    exact sq_nonneg _
  · rw [hp0, hp] at hy
    have hnonneg : ∀ i ∈ Finset.univ, 0 ≤ (y i - p i)^2 := fun i _ => sq_nonneg _
    have h0 : ∀ i ∈ Finset.univ, (y i - p i)^2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hy
    funext i
    have hi := h0 i (Finset.mem_univ i)
    have hsub : y i - p i = 0 := sq_eq_zero_iff.mp hi
    linarith

/-- Lemma 2 (full form): under heterogeneous consistency terms, Paradigm E has
no nonzero stationary point, while the Paradigm I objective always has a
unique minimizer. The appended penalty fails; the internalized objective works;
context can only live inside a single generative objective. -/
theorem lemma2_full {d : Depth} {i j : Pixel} (hHetero : kappa d i ≠ kappa d j) :
    (¬ ∃ lambda : ℝ, lambda ≠ 0 ∧
      ParadigmEFirstOrder d lambda i ∧ ParadigmEFirstOrder d lambda j)
    ∧ ∀ pred : Depth → ℝ, IsParadigmI pred →
        ∃ p : Depth, (∀ y, pred p ≤ pred y) ∧ (∀ y, pred y = pred p → y = p) :=
  ⟨lemma2_E_stationary_infeasible hHetero, fun _ h => paradigmI_unique_minimizer h⟩

/-- Heterogeneous consistency terms ⇒ non-constant depth field. -/
theorem hetero_gives_nonconst
  {d : Depth} {i j : Pixel}
  (hK : kappa d i ≠ kappa d j) :
  ∃ x y : Pixel, d x ≠ d y := by
  by_contra hconst
  have huni : ∀ x y : Pixel, d x = d y := by
    intro x y
    by_cases h : d x = d y <;> try assumption
    exfalso; exact hconst ⟨x, y, h⟩
  have hzero (p : Pixel) : kappa d p = 0 := by
    unfold kappa
    refine Finset.sum_eq_zero ?_
    intro q hq
    linarith [huni p q]
  have hkappa_eq : kappa d i = kappa d j := by
    rw [hzero i, hzero j]
  exact hK hkappa_eq

/-! ## 6. Proposition 4: neural networks are Mode B (frozen weights)
and not Mode A -/

def neuralRule (W : ℝ) (d : Depth) : ℝ := W * (d 0 - d 1)

theorem neural_isModeB (W : ℝ) : IsModeB W (neuralRule W) := by
  intro d
  rfl

theorem neural_not_modeA
  (W : ℝ) (hW : W ≠ 0)
  (d e : Depth) (hd0 : d 0 = e 0) (hd1 : d 1 ≠ e 1) :
  ¬ IsModeA (neuralRule W) := by
  intro hA
  rcases hA with ⟨Φ, hΦ⟩
  have hRd : neuralRule W d = Φ (d 0) := hΦ d
  have hRe : neuralRule W e = Φ (e 0) := hΦ e
  unfold neuralRule at hRd hRe
  have hval : W * (d 0 - d 1) = W * (e 0 - e 1) := by
    calc
      W * (d 0 - d 1) = Φ (d 0) := hRd
      _ = Φ (e 0) := by rw [hd0]
      _ = W * (e 0 - e 1) := by rw [← hRe]
  have hcore : (d 0 - d 1) = (e 0 - e 1) := by
    exact (mul_left_cancel₀ hW) hval
  have hfeq : d 1 = e 1 := by
    nlinarith [hcore, hd0]
  exact hd1 hfeq

/-! ## 7. Lemma 3: a measure framework with explicit premises,
plus toy instantiation

Lemma 3 of the paper: the generalization requirement ⇒ the rule is Mode A.
The argument rests on measure theory (tail realization, positive risk gap,
non-negative minimum risk). Tail realization holds for every distribution
(the mean inequality: a random variable exceeds its mean with positive
probability); on the Lean side it is still included in premise form, to keep
the derivation explicit and to avoid extra measure structure.
Per Route A, all measure premises are **listed explicitly as theorem
hypotheses**, giving a zero-`sorry` deductive skeleton; "positive risk gap" is
substantiated by the two-sided toy `toy_positive_gap`, which combines
`modeB_positive_gap` with `modeA_loss_attained` and `modeA_loss_lower_bound`. -/

/-- Measure-theoretic setup: loss, risk (expectation), and the gap to the
minimum risk. -/
structure MeasureSetup where
  lossR : (Depth → ℝ) → Depth → ℝ         -- ℓ(R, d)
  riskP : (Depth → ℝ) → ℝ                 -- E_P[ℓ(R,·)]
  riskMin : (Depth → ℝ) → ℝ               -- min_{R'} E_P[ℓ(R',·)]
  gapP : (Depth → ℝ) → ℝ                  -- risk R − riskMin
  gap_def : ∀ R : Depth → ℝ, gapP R = riskP R - riskMin R   -- defining equation of gap

/-- Generalization requirement: the loss is bounded on every input of the
test distribution. -/
def GeneralizationBound (m : MeasureSetup) (ε : ℝ) (R : Depth → ℝ) : Prop :=
  ∀ d : Depth, m.lossR R d ≤ ε

/-- Corollary: non-negative minimum risk ⇒ gap ≤ risk (pure algebra from the
defining equation of gap). -/
theorem gap_le_risk_of_nonneg
  (m : MeasureSetup) (R : Depth → ℝ)
  (hNonnegMin : m.riskMin R ≥ 0) :
  m.gapP R ≤ m.riskP R := by
  rw [m.gap_def R]
  linarith

/-- Lemma 3 (final, zero sorry): under the explicit measure premises (tail
realization, non-negative minimum risk, risk gap above the bound), the
generalization bound cannot hold.
Tail realization means some input attains a loss no smaller than the risk;
it holds for every distribution (mean inequality).
Proof: non-negative minimum risk ⇒ gap ≤ risk (corollary), combined with
gap > ε gives risk > ε; tail realization plus the generalization bound gives
risk ≤ loss(d0) ≤ ε, contradiction. -/
theorem lemma3_final2
  (m : MeasureSetup)
  (ε : ℝ) (_hε : ε > 0)
  (R : Depth → ℝ)
  (hTail : ∃ d : Depth, m.lossR R d ≥ m.riskP R)  -- tail realization: some input has loss ≥ risk
  (hGapPositive : m.gapP R > ε)                   -- risk gap above the bound
  (hNonnegMin : m.riskMin R ≥ 0)                  -- non-negative minimum risk
  :
  ¬ GeneralizationBound m ε R := by
  intro hBound
  rcases hTail with ⟨d0, hTail0⟩
  have hb : m.lossR R d0 ≤ ε := hBound d0
  have hrisk : m.riskP R ≤ ε := le_trans hTail0 hb
  have hGapLe : m.gapP R ≤ m.riskP R := gap_le_risk_of_nonneg m R hNonnegMin
  have hriskgt : m.riskP R > ε := by
    linarith [hGapPositive, hGapLe]
  linarith

/-- The target assignment of the demanded rule: varies jointly with evidence
and context. -/
def targetRule (d : Depth) : ℝ := d 0 * d 1

/-- Toy instantiation of Lemma 3: when the demanded rule varies jointly with
evidence and context, every Mode B rule has total loss bounded below by the
positive constant 1 on the three-point open-set sample.
On the points (1,0), (0,1), (1,1), the fixed linear form W·(d0−d1) fitting the
first two points forces W=0, while the third point demands 0=1, so positive
loss is unavoidable; this is exactly the shape of the `hGapPositive` premise
of `lemma3_final2` in the toy model. -/
theorem modeB_positive_gap {W : ℝ} {R : Depth → ℝ} (hB : IsModeB W R) :
    1 ≤ (R ![1, 0, 0, 0] - targetRule ![1, 0, 0, 0]) ^ 2
      + (R ![0, 1, 0, 0] - targetRule ![0, 1, 0, 0]) ^ 2
      + (R ![1, 1, 0, 0] - targetRule ![1, 1, 0, 0]) ^ 2 := by
  rw [hB ![1, 0, 0, 0], hB ![0, 1, 0, 0], hB ![1, 1, 0, 0]]
  simp [targetRule]
  nlinarith [sq_nonneg W]

/-- Toy, Mode A side (lower bound): every evidence-only rule R(d) = Φ(d 0)
has total loss at least 1/2 on the three-point sample. Writing u = Φ 1 and
v = Φ 0, the total is u² + v² + (u − 1)² = 2(u − 1/2)² + v² + 1/2. The toy's
demand d 0 * d 1 depends on the context pixel, so no evidence-only rule can
attain zero loss here; the toy demonstrates the gap mechanism, not Mode A
completeness. -/
theorem modeA_loss_lower_bound {R : Depth → ℝ} (hA : IsModeA R) :
    1 / 2 ≤ (R ![1, 0, 0, 0] - targetRule ![1, 0, 0, 0]) ^ 2
      + (R ![0, 1, 0, 0] - targetRule ![0, 1, 0, 0]) ^ 2
      + (R ![1, 1, 0, 0] - targetRule ![1, 1, 0, 0]) ^ 2 := by
  rcases hA with ⟨Φ, hΦ⟩
  rw [hΦ ![1, 0, 0, 0], hΦ ![0, 1, 0, 0], hΦ ![1, 1, 0, 0]]
  simp [targetRule]
  nlinarith [sq_nonneg (Φ 1 - 1 / 2), sq_nonneg (Φ 0)]

/-- Toy, Mode A side (attainment): the bound 1/2 is attained by the
evidence-only rule R(d) = d 0 / 2. -/
theorem modeA_loss_attained :
    ∃ R : Depth → ℝ, IsModeA R ∧
      (R ![1, 0, 0, 0] - targetRule ![1, 0, 0, 0]) ^ 2
        + (R ![0, 1, 0, 0] - targetRule ![0, 1, 0, 0]) ^ 2
        + (R ![1, 1, 0, 0] - targetRule ![1, 1, 0, 0]) ^ 2 = 1 / 2 := by
  refine ⟨fun d => d 0 / 2, ⟨fun x => x / 2, fun _ => rfl⟩, ?_⟩
  simp only [targetRule, Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Toy substantiation of the positive risk gap (criterion P4 in miniature):
on the three-point sample there is an evidence-only (Mode A) rule whose total
loss beats every frozen (Mode B) rule's total loss by at least 1/2. -/
theorem toy_positive_gap {W : ℝ} {RB : Depth → ℝ} (hB : IsModeB W RB) :
    ∃ RA : Depth → ℝ, IsModeA RA ∧
      (RA ![1, 0, 0, 0] - targetRule ![1, 0, 0, 0]) ^ 2
        + (RA ![0, 1, 0, 0] - targetRule ![0, 1, 0, 0]) ^ 2
        + (RA ![1, 1, 0, 0] - targetRule ![1, 1, 0, 0]) ^ 2 + 1 / 2
      ≤ (RB ![1, 0, 0, 0] - targetRule ![1, 0, 0, 0]) ^ 2
        + (RB ![0, 1, 0, 0] - targetRule ![0, 1, 0, 0]) ^ 2
        + (RB ![1, 1, 0, 0] - targetRule ![1, 1, 0, 0]) ^ 2 := by
  obtain ⟨RA, hA, hRA⟩ := modeA_loss_attained
  have hB1 := modeB_positive_gap hB
  exact ⟨RA, hA, by linarith⟩

/-! ### Evidence-computable variant of the toy (Assumption A0)

The toy above reads its demand from the context coordinate, so no
evidence-instantiated rule can be exact on it and its benchmark risk is the
positive constant 1/2. The variant below uses a demand computable from evidence
alone, which is the case Assumption A0 is about. On the same three-point sample
a constructive evidence-instantiated rule then attains the optimal risk 0, so
the whole frozen loss of 3/2 is gap: the benchmark risk vanishes, and this is the
A0 instance of the barrier-to-gap floor of the paper's Section 5.4. -/

/-- Evidence-computable demand of the variant: the demanded value is an analytic
function of the evidence pixel, hence giveable at inference time by evidence and
analytic means (Assumption A0). -/
def evidenceTarget (d : Depth) : ℝ := (d 0)^2

/-- Variant, frozen side: every Mode B rule has total loss at least 3/2 on the
three-point sample. Writing u = W, the total is (u − 1)² + u² + 1, whose minimum
over u is 3/2 at u = 1/2. -/
theorem modeB_evidence_gap {W : ℝ} {R : Depth → ℝ} (hB : IsModeB W R) :
    3 / 2 ≤ (R ![1, 0, 0, 0] - evidenceTarget ![1, 0, 0, 0]) ^ 2
      + (R ![0, 1, 0, 0] - evidenceTarget ![0, 1, 0, 0]) ^ 2
      + (R ![1, 1, 0, 0] - evidenceTarget ![1, 1, 0, 0]) ^ 2 := by
  rw [hB ![1, 0, 0, 0], hB ![0, 1, 0, 0], hB ![1, 1, 0, 0]]
  simp [evidenceTarget]
  nlinarith [sq_nonneg (W - 1 / 2)]

/-- Variant, Mode A side: the constructive rule R(d) = (d 0)² is Mode A and
attains total loss 0 on the same sample, hence the optimal risk. The demand is a
function of the evidence alone, so this rule recovers it exactly. -/
theorem modeA_evidence_attained :
    ∃ R : Depth → ℝ, IsModeA R ∧
      (R ![1, 0, 0, 0] - evidenceTarget ![1, 0, 0, 0]) ^ 2
        + (R ![0, 1, 0, 0] - evidenceTarget ![0, 1, 0, 0]) ^ 2
        + (R ![1, 1, 0, 0] - evidenceTarget ![1, 1, 0, 0]) ^ 2 = 0 := by
  refine ⟨fun d => (d 0)^2, ⟨fun x => x^2, fun _ => rfl⟩, ?_⟩
  simp [evidenceTarget]

/-- Variant, two-sided: on the same sample an evidence-instantiated (Mode A) rule
attains the optimal risk 0 while every frozen (Mode B) rule's loss is at least
3/2, so the benchmark risk vanishes and the whole frozen loss is gap. -/
theorem evidence_gap_is_full {W : ℝ} {RB : Depth → ℝ} (hB : IsModeB W RB) :
    ∃ RA : Depth → ℝ, IsModeA RA ∧
      ((RA ![1, 0, 0, 0] - evidenceTarget ![1, 0, 0, 0]) ^ 2
        + (RA ![0, 1, 0, 0] - evidenceTarget ![0, 1, 0, 0]) ^ 2
        + (RA ![1, 1, 0, 0] - evidenceTarget ![1, 1, 0, 0]) ^ 2 = 0)
      ∧ 3 / 2 ≤ (RB ![1, 0, 0, 0] - evidenceTarget ![1, 0, 0, 0]) ^ 2
        + (RB ![0, 1, 0, 0] - evidenceTarget ![0, 1, 0, 0]) ^ 2
        + (RB ![1, 1, 0, 0] - evidenceTarget ![1, 1, 0, 0]) ^ 2 := by
  obtain ⟨RA, hA, hRA⟩ := modeA_evidence_attained
  exact ⟨RA, hA, hRA, modeB_evidence_gap hB⟩

/-! ## 8. Criteria and Theorem 5 -/

structure System where
  obs : Observation
  depth : Depth

/-- Criterion P1: the observation is ill-posed. -/
def P1 (sys : System) : Prop := IllPosed sys.obs

/-- Criterion P2: heterogeneous consistency. -/
def P2 (sys : System) : Prop :=
  ∃ i j : Pixel, IsBoundary i ∧ IsInterior j ∧ kappa sys.depth i ≠ kappa sys.depth j

/-- Criterion P3 (open set): the evidence pixel is pinned by observation;
the context pixel is unobserved. -/
def P3 (sys : System) : Prop :=
  sys.obs.mask 0 = true ∧ sys.obs.mask 1 = false

/-- Open set ⇒ ill-posed: the mask shape of criterion P3 directly gives the
forking pair of Definition 1. -/
theorem p3_implies_p1 (sys : System) (h : P3 sys) : P1 sys :=
  illPosed_of_hole h.2

/-- Open-set construction: under P3, one evidence is compatible with two
structure fields that differ at the context pixel, and both fields agree with
the observation on the mask. -/
theorem collision_of_masked {obs : Observation}
    (_h0 : obs.mask 0 = true) (h1 : obs.mask 1 = false) :
    ∃ d e : Depth, d 0 = e 0 ∧ d 1 ≠ e 1 ∧
      (∀ i, obs.mask i = true → d i = obs.value i) ∧
      (∀ i, obs.mask i = true → e i = obs.value i) := by
  have h01 : ¬ (0 : Pixel) = 1 := by decide
  refine ⟨fun i => if i = 1 then (0 : ℝ) else obs.value i,
          fun i => if i = 1 then (1 : ℝ) else obs.value i, ?_, ?_, ?_, ?_⟩
  · simp [h01]
  · simp
  · intro i hi
    have hij : ¬ i = 1 := by
      intro h
      subst h
      rw [h1] at hi
      exact Bool.noConfusion hi
    simp [hij]
  · intro i hi
    have hij : ¬ i = 1 := by
      intro h
      subst h
      rw [h1] at hi
      exact Bool.noConfusion hi
    simp [hij]

/-- Direct consequence of criterion P2: heterogeneous consistency terms ⇒
the structure field is non-constant. -/
theorem p2_gives_nonconst (sys : System) (hP2 : P2 sys) :
    ∃ x y : Pixel, sys.depth x ≠ sys.depth y := by
  rcases hP2 with ⟨i, j, _, _, hK⟩
  exact hetero_gives_nonconst hK

/-- Theorem 5: under criterion P3 (open-set collision sample pair), the
network rule (frozen weights) is not Mode A.
The deduction actually consumes the collision pair supplied by P3 via
`collision_of_masked`; the heterogeneity criterion P2 is consumed at Lemmas 1
and 2. -/
theorem theorem5
  (sys : System)
  (hP3 : P3 sys)
  (W : ℝ) (hW : W ≠ 0) :
  ¬ IsModeA (neuralRule W) := by
  obtain ⟨d, e, hd0, hd1, -, -⟩ := collision_of_masked hP3.1 hP3.2
  exact neural_not_modeA W hW d e hd0 hd1

/-! ## 8.5 Final theorem: the conjunctive composition of Lemma 3 and
Theorem 5 -/

/-- Final theorem finale: under criterion P3 and the measure premises of
Lemma 3, a frozen-weight network rule is neither Mode A nor capable of the
generalization bound. The algebraic form of the paper's "Proposition 𝒫 is
false": the conjunction of the carrier side (not Mode A) and the
generalization side (generalization impossible). -/
theorem finale
  (sys : System)
  (hP3 : P3 sys)
  (m : MeasureSetup) (ε : ℝ) (hε : ε > 0)
  (W : ℝ) (hW : W ≠ 0)
  (hTail : ∃ d : Depth, m.lossR (neuralRule W) d ≥ m.riskP (neuralRule W))
  (hGapPositive : m.gapP (neuralRule W) > ε)
  (hNonnegMin : m.riskMin (neuralRule W) ≥ 0) :
  ¬ IsModeA (neuralRule W) ∧ ¬ GeneralizationBound m ε (neuralRule W) :=
  ⟨theorem5 sys hP3 W hW,
   lemma3_final2 m ε hε (neuralRule W) hTail hGapPositive hNonnegMin⟩

/-! ## 8.7 Pure SPN: Definition 4, Proposition 6, and Theorem 7 -/

/-- Definition 4: inference-time frozen parameters of a pure SPN. The
algebraic form of the dependency graph, sum weights, and leaf parameters is
simplified to a single nonzero scalar, representing non-degenerate structure
and weights. -/
structure SpnParams where
  w : ℝ

/-- The rule of a pure SPN: computed from inference-time frozen parameters and
current evidence; the shape of exact sum-product posteriors matches the
weight-evidence coupling of the neural network. -/
def spnRule (p : SpnParams) (d : Depth) : ℝ := p.w * (d 0 - d 1)

/-- Proposition 6: a pure SPN is Mode B. -/
theorem spn_isModeB (p : SpnParams) : IsModeB p.w (spnRule p) := by
  intro d
  rfl

/-- Corollary of Proposition 6: by the same proof as `neural_not_modeA`, a
pure SPN cannot be Mode A on a sample pair with equal evidence values and
different structure values. -/
theorem spn_not_modeA
  (p : SpnParams) (hW : p.w ≠ 0)
  (d e : Depth) (hd0 : d 0 = e 0) (hd1 : d 1 ≠ e 1) :
  ¬ IsModeA (spnRule p) := by
  intro hA
  rcases hA with ⟨Φ, hΦ⟩
  have hRd : spnRule p d = Φ (d 0) := hΦ d
  have hRe : spnRule p e = Φ (e 0) := hΦ e
  unfold spnRule at hRd hRe
  have hval : p.w * (d 0 - d 1) = p.w * (e 0 - e 1) := by
    calc
      p.w * (d 0 - d 1) = Φ (d 0) := hRd
      _ = Φ (e 0) := by rw [hd0]
      _ = p.w * (e 0 - e 1) := by rw [← hRe]
  have hcore : (d 0 - d 1) = (e 0 - e 1) := by
    exact (mul_left_cancel₀ hW) hval
  have hfeq : d 1 = e 1 := by
    nlinarith [hcore, hd0]
  exact hd1 hfeq

/-- Theorem 7 (pure SPN infeasible): isomorphic to Theorem 5.
Under the collision sample pair from criterion P3, the pure SPN rule is not
Mode A. -/
theorem theorem7_spn
  (sys : System)
  (hP3 : P3 sys)
  (p : SpnParams) (hw : p.w ≠ 0) :
  ¬ IsModeA (spnRule p) := by
  obtain ⟨d, e, hd0, hd1, -, -⟩ := collision_of_masked hP3.1 hP3.2
  exact spn_not_modeA p hw d e hd0 hd1

/-! ## 8.8 The generalization layer from the toy carrier to the continuous
setting

Layer A (domain-free algebraic cores) and Layer B (structured
generalizations). All toy-carrier theorems are retained; this section supplies
their general forms; the consumption pattern of Theorems 5/7 is unchanged.
The bump-based collision construction on the continuous side cites Mathlib's
`ContDiffBump` (Mathlib/Analysis/Calculus/BumpFunction/Basic.lean); this
artifact covers its pointwise form (`collision_general`). -/

open MeasureTheory

/-- Layer A: the algebraic core of Lemma 1, carrier-independent.
If one λ satisfies two first-order conditions, then residuals and consistency
terms are proportional across locations.
The toy side instantiates k = κ; the continuous side instantiates
k = (ℒd)(·). -/
theorem foc_proportionality {ri rj ki kj lambda : ℝ}
    (hi : ri = lambda * ki) (hj : rj = lambda * kj) :
    ri * kj = rj * ki := by
  rw [hi, hj]; ring

/-- Layer B: a general linear criterion for ill-posedness.
A linear observation operator has nontrivial kernel iff two different
structure fields are compatible with one observation: nontrivial kernel is
"hole ⇒ ill-posed", injectivity is "full mask ⇒ uniqueness". -/
theorem illPosed_iff_nontrivial_ker {X Y : Type*}
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (A : X →ₗ[ℝ] Y) :
    (∃ d e : X, d ≠ e ∧ A d = A e) ↔ ∃ v : X, v ≠ 0 ∧ A v = 0 := by
  constructor
  · rintro ⟨d, e, hde, hAe⟩
    exact ⟨d - e, sub_ne_zero.mpr hde, by rw [map_sub, sub_eq_zero]; exact hAe⟩
  · rintro ⟨v, hv, hAv⟩
    exact ⟨v, 0, hv, by simpa using hAv⟩

/-- Layer A: the general form of the open-set collision construction, for an
arbitrary index type. When a free location c0 exists beyond the evidence
location e0, one evidence is compatible with two structure fields. -/
theorem collision_general {ι : Type*} [DecidableEq ι]
    {e0 c0 : ι} (hec : e0 ≠ c0) :
    ∃ d e : ι → ℝ, d e0 = e e0 ∧ d c0 ≠ e c0 := by
  refine ⟨fun i => if i = c0 then (0 : ℝ) else 1, fun _ => 1, ?_, ?_⟩
  · simp [hec]
  · simp

/-- Layer A: evidence dependence (the dependence reading of Mode A on a
general index type). -/
def DependsOnlyOn {ι : Type*} (S : Set ι) (R : (ι → ℝ) → ℝ) : Prop :=
  ∀ d e : (ι → ℝ), (∀ i ∈ S, d i = e i) → R d = R e

/-- Layer A: a non-degenerate frozen rule fails evidence dependence.
A collision pair (equal evidence, different values) rules out Mode A. -/
theorem nondeg_not_dependsOn {ι : Type*} {S : Set ι} {R : (ι → ℝ) → ℝ}
    (hcol : ∃ d e : (ι → ℝ), (∀ i ∈ S, d i = e i) ∧ R d ≠ R e) :
    ¬ DependsOnlyOn S R := by
  intro hdep
  rcases hcol with ⟨d, e, hS, hR⟩
  exact hR (hdep d e hS)

/-- Layer B: the unique minimizer of the Paradigm I objective in an inner
product space. Definiteness gives existence (c = x) and uniqueness. -/
theorem paradigmI_inner_unique {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) :
    (∀ c : E, ‖x - x‖ ≤ ‖x - c‖) ∧ ∀ c : E, ‖x - c‖ = ‖x - x‖ → c = x := by
  constructor
  · intro c
    rw [sub_self, norm_zero]
    exact norm_nonneg _
  · intro c h
    rw [sub_self, norm_zero] at h
    exact (sub_eq_zero.mp (norm_eq_zero.mp h)).symm

/-- Layer B: the measure form of Paradigm I. Vanishing integrated squared
deviation ⇒ almost-everywhere equality. -/
theorem paradigmI_L2_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {x p : Ω → ℝ} (hint : Integrable (fun ω => (x ω - p ω) ^ 2) μ)
    (h0 : ∫ ω, (x ω - p ω) ^ 2 ∂μ = 0) :
    (fun ω => (x ω - p ω) ^ 2) =ᵐ[μ] 0 := by
  have hnn : 0 ≤ᵐ[μ] fun ω => (x ω - p ω) ^ 2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  exact (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0

/-- Layer B: tail realization, demoted from premise to theorem (first-moment
method). For any probability measure and any integrable loss, some input
attains a loss no smaller than the risk. -/
theorem tail_realization {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} (hf : Integrable f μ) :
    ∃ ω, ∫ a, f a ∂μ ≤ f ω :=
  MeasureTheory.exists_integral_le hf

/-- Layer B: the general measure form of Lemma 3.
With an integrable loss, non-negative minimum risk, and risk gap above the
bound, the generalization bound cannot hold.
Tail realization is no longer a premise; it is supplied by
`tail_realization`. -/
theorem lemma3_general {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {loss : Ω → ℝ} (hloss : Integrable loss μ)
    {rmin ε : ℝ} (hmin : 0 ≤ rmin) (hgap : ∫ ω, loss ω ∂μ - rmin > ε)
    (hbound : ∀ ω, loss ω ≤ ε) : False := by
  obtain ⟨ω0, hω0⟩ := tail_realization hloss
  have h1 : ∫ ω, loss ω ∂μ ≤ ε := le_trans hω0 (hbound ω0)
  linarith

/-! ## 8.9 Definition 2 in general (indexed) form, and the general form of
Lemma 1 for a separable data term with a general pairwise potential

Definition 2 of the paper states the context rule as a family `(R_i)_{i∈I}` and
names two specializations: the family is *global* when it is constant across
positions, and *position-wise* otherwise. Sections 3-5 formalize the scalar
specialization (`ContextRule := Depth → ℝ`); this section supplies the indexed
object itself, so that Definition 2's general form and the two claims the paper
makes about it are machine-checked rather than prose.

The point is a separation of the two exclusions. Lemma 1's algebra excludes the
family that is constant *across positions*: for such a family the stationarity
conditions demand one ratio `δ_i / κ_i(d)` at every position, so heterogeneity
of the demand contradicts it. A family with one entry per position solves the
stationarity conditions position by position and therefore escapes the algebra
on any single configuration (`position_wise_escape_witness`). What it does not
escape is the source criterion, because its values are fixed before inference:
one position whose demanded ratio changes between two admissible configurations
excludes every frozen family, whatever its number of entries
(`frozen_family_two_configs_iff`), and the classification is per position and
does not turn on the size of the table (`frozen_table_not_modeA`).

The general potential enters only through the per-position coefficient of the
pairwise term. For a separable data term `Σ_i f_i(d_i)` and an even
differentiable potential `φ`, differentiating the objective in `d_i` gives
`f_i'(d_i) + 2λ Σ_j φ'(d_i - d_j) = 0`, so the algebra below applies with
`δ_i = f_i'(d_i)` and `κ_i(d) = 2 Σ_j φ'(d_i - d_j)`; the squared potential of
Section 5 gives the `kappa` of Section 5 up to the constant factor that Lemma 1
already normalizes. As with Lemma 1, no convexity is used: the stationarity
conditions are necessary conditions, and the exclusion is an exclusion of
stationary points. -/

/-- Definition 2, family form: a context rule is a family indexed by position,
each member mapping a structure field to the strength used at that position. -/
abbrev IndexedContextRule := Pixel → Depth → ℝ

/-- The family induced by a single mapping (the "global" reading). -/
def constantFamily (R : ContextRule) : IndexedContextRule := fun _ d => R d

/-- Definition 2, *global*: the family is constant across positions, so one
mapping is used at every position. -/
def IsGlobalFamily (R : IndexedContextRule) : Prop :=
  ∃ R₀ : ContextRule, ∀ i d, R i d = R₀ d

/-- Definition 2, *position-wise*: the family is not constant. -/
def IsPositionWise (R : IndexedContextRule) : Prop := ¬ IsGlobalFamily R

/-- The single scalar λ of classical regularization: the global family whose one
mapping is constant. -/
def IsScalarFamily (R : IndexedContextRule) : Prop :=
  ∃ lambda : ℝ, ∀ i d, R i d = lambda

/-- A frozen family: one number per position, fixed before inference and hence
independent of the instance. The scalar family is the case of one entry. -/
def IsFrozenFamily (R : IndexedContextRule) : Prop :=
  ∃ W : Pixel → ℝ, ∀ i d, R i d = W i

/-- The scalar family is exactly the global family whose values are frozen:
"the single scalar λ of classical regularization is exactly this case". -/
theorem scalar_iff_global_and_frozen (R : IndexedContextRule) :
    IsScalarFamily R ↔ IsGlobalFamily R ∧ IsFrozenFamily R := by
  constructor
  · intro h
    rcases h with ⟨lambda, hl⟩
    exact ⟨⟨fun _ => lambda, fun i d => hl i d⟩, ⟨fun _ => lambda, fun i d => hl i d⟩⟩
  · rintro ⟨⟨R₀, hR₀⟩, ⟨W, hW⟩⟩
    refine ⟨W 0, fun i d => ?_⟩
    calc R i d = W i := hW i d
      _ = R₀ d := by rw [← hW i d]; exact hR₀ i d
      _ = W 0 := by rw [← hR₀ 0 d]; exact hW 0 d

/-- The indexed first-order condition at a position, in the general form: `δ_i`
is the derivative of the separable data term at position `i` (`δ_i = d_i - x_i`
for the squared data term of Lemma 1), `R i d` is the strength the family
prescribes at that position, and `kappa d i` is the per-position coefficient of
the pairwise term. -/
def GeneralFirstOrder (δ : Pixel → ℝ) (d : Depth) (R : IndexedContextRule)
    (i : Pixel) : Prop :=
  δ i + R i d * kappa d i = 0

/-- The algebraic core of Lemma 1 in general form: it uses neither the quadratic
data term nor the quadratic potential, only the two stationarity equations, which
is why no convexity enters. -/
theorem general_proportionality {δ : Pixel → ℝ} {d : Depth} {lambda : ℝ}
    {i j : Pixel}
    (h1 : δ i + lambda * kappa d i = 0) (h2 : δ j + lambda * kappa d j = 0) :
    δ i * kappa d j = δ j * kappa d i := by
  have e1 : δ i = -(lambda * kappa d i) := by linarith
  have e2 : δ j = -(lambda * kappa d j) := by linarith
  rw [e1, e2]; ring

/-- Minimal obstruction to the scalar family at one configuration: a scalar λ
satisfies the stationarity conditions at every position precisely when the
demanded ratio δ_i/κ_i(d) is the same at every position. Stated cross-multiplied
against a reference position with nonzero coefficient, so no division by κ
appears in the statement. -/
theorem scalar_family_iff_ratio_agrees (δ : Pixel → ℝ) (d : Depth) {k : Pixel}
    (hk : kappa d k ≠ 0) :
    (∃ R : IndexedContextRule, IsScalarFamily R ∧ ∀ i, GeneralFirstOrder δ d R i) ↔
      ∀ i, δ i * kappa d k = δ k * kappa d i := by
  constructor
  · rintro ⟨R, ⟨lambda, hl⟩, hFOC⟩ i
    have h1 : δ i + lambda * kappa d i = 0 := by
      have := hFOC i; unfold GeneralFirstOrder at this; rwa [hl i d] at this
    have h2 : δ k + lambda * kappa d k = 0 := by
      have := hFOC k; unfold GeneralFirstOrder at this; rwa [hl k d] at this
    exact general_proportionality h1 h2
  · intro h
    refine ⟨fun _ _ => -(δ k) / kappa d k,
      ⟨-(δ k) / kappa d k, fun i d' => rfl⟩, fun i => ?_⟩
    unfold GeneralFirstOrder
    have hcancel : (-(δ k) / kappa d k) * kappa d k = -(δ k) := by
      rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hk, mul_one]
    have hprod : (δ i + (-(δ k) / kappa d k) * kappa d i) * kappa d k = 0 := by
      calc (δ i + (-(δ k) / kappa d k) * kappa d i) * kappa d k
          = δ i * kappa d k + ((-(δ k) / kappa d k) * kappa d k) * kappa d i := by ring
        _ = δ i * kappa d k + (-(δ k)) * kappa d i := by rw [hcancel]
        _ = 0 := by linarith [h i]
    exact (mul_eq_zero.mp hprod).resolve_right hk

/-- Minimal impossibility condition for frozen families: a frozen family
satisfies the stationarity conditions at two configurations precisely when, at
every position, the demanded ratio agrees between the two. The condition is
per position, so the number of entries in the table is irrelevant. -/
theorem frozen_family_two_configs_iff (δ δ' : Pixel → ℝ) (d d' : Depth)
    (hκ : ∀ i, kappa d i ≠ 0) :
    (∃ R : IndexedContextRule, IsFrozenFamily R ∧
        (∀ i, GeneralFirstOrder δ d R i) ∧ (∀ i, GeneralFirstOrder δ' d' R i)) ↔
      ∀ i, δ i * kappa d' i = δ' i * kappa d i := by
  constructor
  · rintro ⟨R, ⟨W, hW⟩, h1, h2⟩ i
    have e1 : W i * kappa d i = -(δ i) := by
      have := h1 i; unfold GeneralFirstOrder at this; rw [hW i d] at this; linarith
    have e2 : W i * kappa d' i = -(δ' i) := by
      have := h2 i; unfold GeneralFirstOrder at this; rw [hW i d'] at this; linarith
    have he1 : δ i = -(W i * kappa d i) := by linarith
    have he2 : δ' i = -(W i * kappa d' i) := by linarith
    rw [he1, he2]; ring
  · intro h
    refine ⟨fun i _ => -(δ i) / kappa d i,
      ⟨fun i => -(δ i) / kappa d i, fun i d'' => rfl⟩, ?_, ?_⟩
    · intro i
      simp only [GeneralFirstOrder]
      have hcancel : (-(δ i) / kappa d i) * kappa d i = -(δ i) := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hκ i), mul_one]
      rw [hcancel]; ring
    · intro i
      simp only [GeneralFirstOrder]
      have hratio : (-(δ i) / kappa d i) * kappa d' i
          = -(δ i * kappa d' i / kappa d i) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [hratio, h i, mul_div_cancel_right₀ _ (hκ i)]
      ring

/-- The same obstruction, in the form the paper states it: one single position
whose demanded ratio changes between two admissible configurations excludes every
frozen coefficient family, constant or position-wise. -/
theorem frozen_family_infeasible_of_ratio_differs {δ δ' : Pixel → ℝ} {d d' : Depth}
    {i : Pixel} (hdiff : δ i * kappa d' i ≠ δ' i * kappa d i) :
    ¬ ∃ R : IndexedContextRule, IsFrozenFamily R ∧
        (∀ j, GeneralFirstOrder δ d R j) ∧ (∀ j, GeneralFirstOrder δ' d' R j) := by
  rintro ⟨R, ⟨W, hW⟩, h1, h2⟩
  apply hdiff
  have e1 : W i * kappa d i = -(δ i) := by
    have := h1 i; unfold GeneralFirstOrder at this; rw [hW i d] at this; linarith
  have e2 : W i * kappa d' i = -(δ' i) := by
    have := h2 i; unfold GeneralFirstOrder at this; rw [hW i d'] at this; linarith
  have he1 : δ i = -(W i * kappa d i) := by linarith
  have he2 : δ' i = -(W i * kappa d' i) := by linarith
  rw [he1, he2]; ring

/-- Lemma 1's algebra excludes the constant family only. On one and the same
configuration a frozen family with one entry per position satisfies every
stationarity condition while no scalar family does, so the index is a loophole
for the algebra — and the frozen family is exactly the object the source
criterion then reaches. -/
theorem position_wise_escape_witness {δ : Pixel → ℝ} {d : Depth} {i j : Pixel}
    (hκ : ∀ k, kappa d k ≠ 0)
    (hne : δ i * kappa d j ≠ δ j * kappa d i) :
    (∃ R : IndexedContextRule, IsFrozenFamily R ∧
        IsPositionWise R ∧ ∀ k, GeneralFirstOrder δ d R k) ∧
      ¬ ∃ R : IndexedContextRule, IsScalarFamily R ∧
        ∀ k, GeneralFirstOrder δ d R k := by
  constructor
  · refine ⟨fun k _ => -(δ k) / kappa d k,
      ⟨fun k => -(δ k) / kappa d k, fun k d' => rfl⟩, ?_, ?_⟩
    · rintro ⟨R₀, hR₀⟩
      have h1 : -(δ i) / kappa d i = R₀ d := hR₀ i d
      have h2 : -(δ j) / kappa d j = R₀ d := hR₀ j d
      have hratio : δ i / kappa d i = δ j / kappa d j := by
        have h := h1.trans h2.symm
        rw [neg_div, neg_div, neg_inj] at h
        exact h
      exact hne ((div_eq_div_iff (hκ i) (hκ j)).mp hratio)
    · intro k
      simp only [GeneralFirstOrder]
      have hcancel : (-(δ k) / kappa d k) * kappa d k = -(δ k) := by
        rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ (hκ k), mul_one]
      rw [hcancel]; ring
  · rintro ⟨R, ⟨lambda, hl⟩, hFOC⟩
    refine hne (general_proportionality (lambda := lambda) ?_ ?_)
    · have := hFOC i; unfold GeneralFirstOrder at this; rwa [hl i d] at this
    · have := hFOC j; unfold GeneralFirstOrder at this; rwa [hl j d] at this

/-- The rule a frozen table induces at a position: its entry times a fixed
feature of the structure field. -/
def tableRule (W : Pixel → ℝ) (i : Pixel) : ContextRule := fun d => W i * (d 0 - d 1)

/-- A frozen table does not escape the source criterion. Its rule at a position
is not evidence-instantiated, whatever the number of entries: the classification
is per position, so "one scalar is a parameter table and a million entries are a
parameter table as well". -/
theorem frozen_table_not_modeA (W : Pixel → ℝ) (i : Pixel) (hW : W i ≠ 0)
    (d e : Depth) (hd0 : d 0 = e 0) (hd1 : d 1 ≠ e 1) :
    ¬ IsModeA (tableRule W i) := by
  intro hA
  rcases hA with ⟨Φ, hΦ⟩
  have hRd : tableRule W i d = Φ (d 0) := hΦ d
  have hRe : tableRule W i e = Φ (e 0) := hΦ e
  unfold tableRule at hRd hRe
  have hval : W i * (d 0 - d 1) = W i * (e 0 - e 1) := by
    calc
      W i * (d 0 - d 1) = Φ (d 0) := hRd
      _ = Φ (e 0) := by rw [hd0]
      _ = W i * (e 0 - e 1) := by rw [← hRe]
  have hcore : (d 0 - d 1) = (e 0 - e 1) := mul_left_cancel₀ hW hval
  have hfeq : d 1 = e 1 := by nlinarith [hcore, hd0]
  exact hd1 hfeq

/-! ## 8.10 From the objective to the general first-order condition

Section 8.9 states the demand-ratio algebra for a general pairwise potential and
takes the stationarity condition as given, the same convention Lemma 1 of the
paper uses for the quadratic case. This section removes that gap on the toy
carrier: it differentiates the objective along the coordinate line of one
position, derives the per-position coefficient `KappaPhi` of a general even
differentiable potential, and obtains the stationarity condition from a local
minimum rather than assuming it. The last theorem of the section derives the
paper's first-order condition of Lemma 1 from the quadratic objective, with the
normalization of constant factors made explicit as the scalar `2λ`. -/

/-- The per-position coefficient of a pairwise potential `φ` with derivative
`φ'`: the paper's `κ_i^φ`. For an even `φ` it is the coordinate derivative of the
pairwise term (`PairwiseTerm_hasDerivAt`), and for the squared potential it is
`kappa` up to the constant factor that Lemma 1 normalizes
(`KappaPhi_quadratic`). -/
def KappaPhi (φ' : ℝ → ℝ) (d : Depth) (i : Pixel) : ℝ :=
  2 * ∑ j : Pixel, φ' (d i - d j)

/-- The pairwise term of the objective with a general potential. -/
def PairwiseTerm (φ : ℝ → ℝ) (d : Depth) : ℝ :=
  ∑ a : Pixel, ∑ b : Pixel, φ (d a - d b)

example (d : Depth) (i a b : Pixel) :
    HasDerivAt (fun t : ℝ => Function.update d i t a - Function.update d i t b)
      ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0)) (d i) := by
  by_cases hai : a = i <;> by_cases hbi : b = i
  · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
        = fun _ => 0 := by
      funext t
      rw [hai, hbi, Function.update_self, sub_self]
    rw [hfun]
    simpa [hai, hbi] using hasDerivAt_const (d i) (0 : ℝ)
  · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
        = fun t => t - d b := by
      funext t
      rw [hai, Function.update_self, Function.update_of_ne hbi t d]
    rw [hfun]
    simpa [hai, hbi] using
      (hasDerivAt_id' (d i)).sub_const (d b)
  · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
        = fun t => d a - t := by
      funext t
      rw [hbi, Function.update_of_ne hai t d, Function.update_self]
    rw [hfun]
    simpa [hai, hbi] using
      (hasDerivAt_id' (d i)).const_sub (d a)
  · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
        = fun _ => d a - d b := by
      funext t
      rw [Function.update_of_ne hai t d, Function.update_of_ne hbi t d]
    rw [hfun]
    simpa [hai, hbi] using hasDerivAt_const (d i) (d a - d b)

theorem deriv_odd_of_even {φ φ' : ℝ → ℝ} (heven : ∀ x, φ (-x) = φ x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (x : ℝ) : φ' (-x) = -φ' x := by
  have hcomp : HasDerivAt (fun y : ℝ => φ (-y)) (φ' (-x) * (-1)) x :=
    (hφ (-x)).comp x (hasDerivAt_neg' x)
  rw [funext heven] at hcomp
  have h := (hφ x).unique hcomp
  linarith

private lemma hasDerivAt_pairwise_term {φ φ' : ℝ → ℝ}
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (d : Depth) (i a b : Pixel) :
    HasDerivAt (fun t : ℝ => φ (Function.update d i t a - Function.update d i t b))
      (((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0))
        * φ' (d a - d b)) (d i) := by
  have hinner : HasDerivAt (fun t : ℝ => Function.update d i t a - Function.update d i t b)
      ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0)) (d i) := by
    by_cases hai : a = i <;> by_cases hbi : b = i
    · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
          = fun _ => 0 := by
        funext t
        rw [hai, hbi, Function.update_self, sub_self]
      rw [hfun]
      simpa [hai, hbi] using hasDerivAt_const (d i) (0 : ℝ)
    · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
          = fun t => t - d b := by
        funext t
        rw [hai, Function.update_self, Function.update_of_ne hbi t d]
      rw [hfun]
      simpa [hai, hbi] using (hasDerivAt_id' (d i)).sub_const (d b)
    · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
          = fun t => d a - t := by
        funext t
        rw [hbi, Function.update_of_ne hai t d, Function.update_self]
      rw [hfun]
      simpa [hai, hbi] using (hasDerivAt_id' (d i)).const_sub (d a)
    · have hfun : (fun t : ℝ => Function.update d i t a - Function.update d i t b)
          = fun _ => d a - d b := by
        funext t
        rw [Function.update_of_ne hai t d, Function.update_of_ne hbi t d]
      rw [hfun]
      simpa [hai, hbi] using hasDerivAt_const (d i) (d a - d b)
  have hφ' : HasDerivAt φ (φ' (d a - d b))
      (Function.update d i (d i) a - Function.update d i (d i) b) := by
    rw [Function.update_eq_self]
    exact hφ (d a - d b)
  have h := hφ'.comp (d i) hinner
  rw [mul_comm] at h
  exact h

theorem pairCoef_sum (φ' : ℝ → ℝ) (d : Depth) (i : Pixel)
    (hodd : ∀ x, φ' (-x) = -φ' x) :
    (∑ a : Pixel, ∑ b : Pixel,
        ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0))
          * φ' (d a - d b)) = KappaPhi φ' d i := by
  have hstep : ∀ a b : Pixel,
      ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0))
          * φ' (d a - d b)
        = (if a = i then φ' (d i - d b) else 0)
          - (if b = i then φ' (d a - d i) else 0) := by
    intro a b
    by_cases ha : a = i <;> by_cases hb : b = i <;> simp [ha, hb]
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep a b))]
  have hinner : ∀ a : Pixel,
      (∑ b : Pixel, ((if a = i then φ' (d i - d b) else 0)
          - (if b = i then φ' (d a - d i) else 0)))
        = (∑ b : Pixel, (if a = i then φ' (d i - d b) else 0))
          - ∑ b : Pixel, (if b = i then φ' (d a - d i) else 0) :=
    fun a => by rw [Finset.sum_sub_distrib]
  rw [Finset.sum_congr rfl (fun a _ => hinner a), Finset.sum_sub_distrib]
  have hX : (∑ a : Pixel, ∑ b : Pixel, (if a = i then φ' (d i - d b) else 0))
      = ∑ b : Pixel, φ' (d i - d b) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro a _ ha
      simp [ha]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hY : (∑ a : Pixel, ∑ b : Pixel, (if b = i then φ' (d a - d i) else 0))
      = ∑ a : Pixel, φ' (d a - d i) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hYneg : (∑ a : Pixel, φ' (d a - d i)) = -(∑ a : Pixel, φ' (d i - d a)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h := hodd (d i - d a)
    rwa [neg_sub] at h
  rw [hX, hY, hYneg]
  unfold KappaPhi
  ring

theorem PairwiseTerm_hasDerivAt {φ φ' : ℝ → ℝ} (heven : ∀ x, φ (-x) = φ x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (d : Depth) (i : Pixel) :
    HasDerivAt (fun t : ℝ => PairwiseTerm φ (Function.update d i t))
      (KappaPhi φ' d i) (d i) := by
  have houter : HasDerivAt
      (fun t : ℝ => ∑ a : Pixel, ∑ b : Pixel,
        φ (Function.update d i t a - Function.update d i t b))
      (∑ a : Pixel, ∑ b : Pixel,
        ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0))
          * φ' (d a - d b)) (d i) := by
    refine HasDerivAt.fun_sum
      (u := (Finset.univ : Finset Pixel))
      (A := fun a t => ∑ b : Pixel, φ (Function.update d i t a - Function.update d i t b))
      (A' := fun a => ∑ b : Pixel,
        ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0))
          * φ' (d a - d b)) ?_
    intro a _
    exact HasDerivAt.fun_sum
      (u := (Finset.univ : Finset Pixel))
      (A := fun b t => φ (Function.update d i t a - Function.update d i t b))
      (A' := fun b => ((if a = i then (1 : ℝ) else 0) - (if b = i then (1 : ℝ) else 0))
        * φ' (d a - d b)) (fun b _ => hasDerivAt_pairwise_term hφ d i a b)
  rw [pairCoef_sum φ' d i (deriv_odd_of_even heven hφ)] at houter
  exact houter

/-- The objective of a separable data term with a general pairwise potential. -/
def GeneralObjective (φ : ℝ → ℝ) (f : Pixel → ℝ → ℝ) (lambda : ℝ) (d : Depth) : ℝ :=
  (∑ k : Pixel, f k (d k)) + lambda * PairwiseTerm φ d

theorem dataTerm_hasDerivAt {f f' : Pixel → ℝ → ℝ}
    (hf : ∀ k x, HasDerivAt (f k) (f' k x) x) (d : Depth) (i : Pixel) :
    HasDerivAt (fun t : ℝ => ∑ k : Pixel, f k (Function.update d i t k))
      (f' i (d i)) (d i) := by
  have hterm : ∀ k : Pixel, HasDerivAt (fun t : ℝ => f k (Function.update d i t k))
      (if k = i then f' k (d i) else 0) (d i) := by
    intro k
    by_cases hk : k = i
    · rw [hk]
      have hfun : (fun t : ℝ => f i (Function.update d i t i)) = f i := by
        funext t
        rw [Function.update_self]
      rw [hfun]
      simpa using hf i (d i)
    · have hfun : (fun t : ℝ => f k (Function.update d i t k)) = fun _ => f k (d k) := by
        funext t
        rw [Function.update_of_ne hk t d]
      rw [hfun]
      simpa [hk] using hasDerivAt_const (d i) (f k (d k))
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset Pixel))
    (A := fun k t => f k (Function.update d i t k))
    (A' := fun k => if k = i then f' k (d i) else 0) (fun k _ => hterm k)
  have hsingle : (∑ k : Pixel, (if k = i then f' k (d i) else 0)) = f' i (d i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [hsingle] at hsum
  exact hsum

theorem GeneralObjective_hasDerivAt {φ φ' : ℝ → ℝ} {f f' : Pixel → ℝ → ℝ}
    (heven : ∀ x, φ (-x) = φ x) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hf : ∀ k x, HasDerivAt (f k) (f' k x) x) (lambda : ℝ) (d : Depth)
    (i : Pixel) :
    HasDerivAt (fun t : ℝ => GeneralObjective φ f lambda (Function.update d i t))
      (f' i (d i) + lambda * KappaPhi φ' d i) (d i) := by
  have hdata := dataTerm_hasDerivAt hf d i
  have hpair := (PairwiseTerm_hasDerivAt heven hφ d i).const_mul lambda
  have hsum := hdata.add hpair
  convert hsum using 1
  funext t
  rfl

theorem general_first_order_of_local_min {φ φ' : ℝ → ℝ} {f f' : Pixel → ℝ → ℝ}
    (heven : ∀ x, φ (-x) = φ x) (hφ : ∀ x, HasDerivAt φ (φ' x) x)
    (hf : ∀ k x, HasDerivAt (f k) (f' k x) x) (lambda : ℝ) (d : Depth) (i : Pixel)
    (hmin : IsLocalMin (fun t : ℝ =>
      GeneralObjective φ f lambda (Function.update d i t)) (d i)) :
    f' i (d i) + lambda * KappaPhi φ' d i = 0 :=
  hmin.hasDerivAt_eq_zero (GeneralObjective_hasDerivAt heven hφ hf lambda d i)


theorem hasDerivAt_sq (x : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
  simpa using hasDerivAt_pow 2 x

theorem KappaPhi_quadratic (d : Depth) (i : Pixel) :
    KappaPhi (fun x : ℝ => 2 * x) d i = 4 * kappa d i := by
  unfold KappaPhi kappa
  rw [Finset.mul_sum, Finset.mul_sum]
  ring_nf

theorem FirstOrder_of_quadratic_local_min (x d : Depth) (lambda : ℝ) (i : Pixel)
    (hmin : IsLocalMin (fun t : ℝ => GeneralObjective (fun y : ℝ => y ^ 2)
      (fun k t => (x k - t) ^ 2) lambda (Function.update d i t)) (d i)) :
    FirstOrder x d (2 * lambda) i := by
  have heven : ∀ y : ℝ, (fun z : ℝ => z ^ 2) (-y) = (fun z : ℝ => z ^ 2) y := by
    intro y
    ring
  have hf : ∀ (k : Pixel) (t : ℝ), HasDerivAt (fun s : ℝ => (x k - s) ^ 2) (2 * (t - x k)) t := by
    intro k t
    have hinner : HasDerivAt (fun s : ℝ => x k - s) (-1) t :=
      (hasDerivAt_id' t).const_sub (x k)
    have h := (hasDerivAt_sq (x k - t)).comp t hinner
    convert h using 1
    · ext s
      rfl
    · ring
  have hfoc := general_first_order_of_local_min heven hasDerivAt_sq hf lambda d i hmin
  rw [KappaPhi_quadratic] at hfoc
  unfold FirstOrder
  linarith

/-! ## 9. Check summary -/

#check illPosed_of_hole
#check not_illPosed_of_full
#check p3_implies_p1
#check collision_of_masked
#check lemma1_sharp
#check lemma1_final
#check lemma2_E_stationary_infeasible
#check paradigmI_unique_minimizer
#check lemma2_full
#check hetero_gives_nonconst
#check p2_gives_nonconst
#check neural_isModeB
#check neural_not_modeA
#check gap_le_risk_of_nonneg
#check lemma3_final2
#check targetRule
#check modeB_positive_gap
#check modeA_loss_lower_bound
#check modeA_loss_attained
#check toy_positive_gap
#check evidenceTarget
#check modeB_evidence_gap
#check modeA_evidence_attained
#check evidence_gap_is_full
#check theorem5
#check finale
#check spn_isModeB
#check spn_not_modeA
#check theorem7_spn
#check foc_proportionality
#check illPosed_iff_nontrivial_ker
#check collision_general
#check nondeg_not_dependsOn
#check paradigmI_inner_unique
#check paradigmI_L2_ae
#check tail_realization
#check lemma3_general
#check SpnParams
#check IsParadigmI
#check IndexedContextRule
#check constantFamily
#check IsGlobalFamily
#check IsPositionWise
#check IsScalarFamily
#check IsFrozenFamily
#check scalar_iff_global_and_frozen
#check GeneralFirstOrder
#check general_proportionality
#check scalar_family_iff_ratio_agrees
#check frozen_family_two_configs_iff
#check frozen_family_infeasible_of_ratio_differs
#check position_wise_escape_witness
#check tableRule
#check frozen_table_not_modeA
#check KappaPhi
#check PairwiseTerm
#check GeneralObjective
#check deriv_odd_of_even
#check pairCoef_sum
#check PairwiseTerm_hasDerivAt
#check dataTerm_hasDerivAt
#check GeneralObjective_hasDerivAt
#check general_first_order_of_local_min
#check hasDerivAt_sq
#check KappaPhi_quadratic
#check FirstOrder_of_quadratic_local_min

end FormalProof
