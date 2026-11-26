import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.AffineScheme
import PrimalitySheafVerification.ManuscriptAudit.FieldEtaleGaloisPoints

/-! Finite Galois spectra refine every covering sieve of the terminal small étale object. -/

namespace ManuscriptAudit.FieldEtaleGaloisCovers

open CategoryTheory AlgebraicGeometry
open Opposite
open FieldEtaleGaloisPoints

noncomputable section

def terminalObject (K : Type) [Field K] : (Spec (CommRingCat.of K)).Etale :=
  Scheme.Etale.mk (𝟙 (Spec (CommRingCat.of K)))

def galoisObject (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsGalois K L] : (Spec (CommRingCat.of K)).Etale := by
  letI := finiteGalois_spec_map_etale K L
  exact Scheme.Etale.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))

def galoisArrow (K L : Type) [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] [IsGalois K L] : galoisObject K L ⟶ terminalObject K :=
  MorphismProperty.Over.homMk (galoisObject K L).hom (Category.comp_id _)

private theorem terminal_hom_eq (K : Type) [Field K] {U : (Spec (CommRingCat.of K)).Etale}
    (a b : U ⟶ terminalObject K) : a = b := by
  have ha : a.left = U.hom := by
    simpa [terminalObject] using MorphismProperty.Over.w a
  have hb : b.left = U.hom := by
    simpa [terminalObject] using MorphismProperty.Over.w b
  ext : 1
  exact ha.trans hb.symm

set_option backward.isDefEq.respectTransparency false in
theorem coveringSieve_has_finiteGalois_arrow (K : Type) [Field K]
    (R : Sieve (terminalObject K))
    (hR : R ∈ (Spec (CommRingCat.of K)).smallEtaleTopology (terminalObject K)) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
        (_ : IsGalois K L), R (galoisArrow K L) := by
  let X := Spec (CommRingCat.of K)
  obtain ⟨V, hOver, hEtale, hCover⟩ :=
    (Scheme.mem_smallGrothendieckTopology (terminalObject K) R).mp hR
  letI := hOver
  let x : (terminalObject K).left := Classical.choice
    (inferInstance : Nonempty (PrimeSpectrum K))
  obtain ⟨i, y, _⟩ := V.exists_eq x
  let U := V.X i
  let A := U.affineOpenCover
  let j := A.idx y
  have hj : ∃ z : Spec (A.X j), A.f j z = y := A.covers y
  obtain ⟨z, _⟩ := hj
  let B := A.X j
  letI : Nontrivial B := PrimeSpectrum.nontrivial (show PrimeSpectrum B from z)
  let a : Spec B ⟶ U := A.f j
  letI : Etale (U ↘ X) := hEtale i
  letI : Etale a := inferInstanceAs (Etale (A.f j))
  let f : Spec B ⟶ X := a ≫ (U ↘ X)
  letI : Etale f := inferInstanceAs (Etale (a ≫ (U ↘ X)))
  let m : CommRingCat.of K ⟶ B := (Scheme.Spec.preimage f).unop
  have hm : Spec.map m = f := Scheme.Spec.image_preimage f
  letI : Etale (Spec.map m) := hm.symm ▸ (inferInstance : Etale f)
  obtain ⟨L, hField, hAlg, hFinite, hGalois, g, hg⟩ := exists_finiteGalois_spec_factor K B m
  letI := hField
  letI := hAlg
  letI := hFinite
  letI := hGalois
  let Zi : X.Etale := U.asOverProp X (hEtale i)
  let v : Zi ⟶ terminalObject K := (V.f i).asOverProp X
  have hv : R v := hCover (Presieve.ofArrows.mk i)
  let u : galoisObject K L ⟶ Zi :=
    MorphismProperty.Over.homMk (g ≫ a) (by
      change (g ≫ a) ≫ (U ↘ X) = Spec.map (CommRingCat.ofHom (algebraMap K L))
      rw [Category.assoc]
      exact (congrArg (fun t => g ≫ t) hm.symm).trans hg)
  have h := R.downward_closed hv u
  rw [terminal_hom_eq K (u ≫ v) (galoisArrow K L)] at h
  exact ⟨L, hField, hAlg, hFinite, hGalois, h⟩

end
end ManuscriptAudit.FieldEtaleGaloisCovers

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FieldEtaleGaloisCovers.coveringSieve_has_finiteGalois_arrow
  let ax ← collectAxioms name
  let bad := ax.filter fun x => ![``propext, ``Classical.choice, ``Quot.sound].contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
