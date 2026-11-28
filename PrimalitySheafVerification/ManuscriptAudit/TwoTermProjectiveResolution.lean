import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-! An exact presentation by two projective objects gives the genuine
two-term projective resolution, with explicit native differentials. -/

namespace ManuscriptAudit.TwoTermProjectiveResolution

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C] {A B X : C}

private def stages (A B : C) : ℕ → C
  | 0 => B
  | 1 => A
  | _ + 2 => 0

private def boundary (f : A ⟶ B) :
    ∀ n : ℕ, stages A B (n+1) ⟶ stages A B n
  | 0 => f
  | _ + 1 => 0

/-- The actual chain complex supported in degrees zero and one. -/
def complex (f : A ⟶ B) : ChainComplex C ℕ :=
  ChainComplex.of (stages A B) (boundary f) (by
    intro n
    cases n <;> simp [boundary])

theorem d_one_zero (f : A ⟶ B) : (complex f).d 1 0 = f := by
  change ChainComplex.of.d (stages A B) (boundary f) (0 + 1) 0 = f
  exact ChainComplex.of_d (stages A B) (boundary f) 0

theorem d_two_one (f : A ⟶ B) : (complex f).d 2 1 = 0 := by
  change ChainComplex.of.d (stages A B) (boundary f) (1 + 1) 1 = 0
  exact ChainComplex.of_d (stages A B) (boundary f) 1

private theorem exact_succ (f : A ⟶ B) [Mono f] (n : ℕ) :
    (complex f).ExactAt (n+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n+1+1) (n+1) n (by simp) (by simp)]
  cases n with
  | zero =>
      let S := (complex f).sc' 2 1 0
      change S.Exact
      have hf : S.f = 0 := d_two_one f
      have hg : S.g = f := d_one_zero f
      apply (S.exact_iff_mono hf).2
      rw [hg]
      infer_instance
  | succ n =>
      apply ShortComplex.exact_of_isZero_X₂
      change IsZero (0 : C)
      exact isZero_zero C

private def augmentation (f : A ⟶ B) (q : B ⟶ X) (w : f ≫ q = 0) :
    complex f ⟶ (ChainComplex.single₀ C).obj X :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨q, by rw [d_one_zero, w]⟩

private theorem augmentation_f_zero (f : A ⟶ B) (q : B ⟶ X) (w : f ≫ q = 0) :
    (augmentation f q w).f 0 = q :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero q _

/-- The literal two-term complex resolves the actual degree-zero quotient. -/
def resolution (f : A ⟶ B) (q : B ⟶ X) (w : f ≫ q = 0)
    [Projective A] [Projective B] [Mono f] [Epi q]
    (h : (ShortComplex.mk f q w).Exact) : ProjectiveResolution X where
  complex := complex f
  projective n := by
    obtain (_ | _ | n) := n
    · change Projective B
      infer_instance
    · change Projective A
      infer_instance
    · change Projective (0 : C)
      infer_instance
  π := augmentation f q w
  quasiIso := ⟨fun n ↦ by
    cases n with
    | zero =>
        rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
        · change (ShortComplex.mk ((complex f).d 1 0) ((augmentation f q w).f 0) _).Exact ∧
            Epi ((augmentation f q w).f 0)
          rw [augmentation_f_zero, d_one_zero]
          exact ⟨h, inferInstance⟩
        all_goals rfl
    | succ n =>
        rw [quasiIsoAt_iff_exactAt']
        · exact exact_succ f n
        · exact ChainComplex.exactAt_succ_single_obj _ _⟩

end
end ManuscriptAudit.TwoTermProjectiveResolution

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.TwoTermProjectiveResolution.resolution
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
