import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper8EtaLevelZeroMode
import PrimalitySheafVerification.ManuscriptAudit.Paper8OddCrossCuspRows
import PrimalitySheafVerification.ManuscriptAudit.Paper8SawtoothDistribution

/-!
# The finite eta phase for the odd cross-cusp sums

For cusp scalings I and S diag(2,1/2), Andersen–Duke, arXiv:1801.08174,
§3 formula (3.3), uses modulus 2D and entries 2a,d/2. The shifted
frequencies are 1/24 and 1/6. Dividing the explicit eta multiplier of
the integral row by the eta multiplier of S gives its transported phase.
These finite identities use the explicit primary phase formulas.
-/

namespace ManuscriptAudit.Paper8OddCrossCuspPhase

open Paper8ContourResidueWeights (dedekindSum)
open Paper8SawtoothDistribution (sawtooth_int_translate)
open Paper8HolomorphicPartPhase (periodCoefficient)
open Paper8EtaLevelZeroMode (referenceEntry)
open Paper8OddCrossCuspRows (chiFour)

noncomputable section

theorem dedekind_translate {D : ℕ} (hD : 0 < D) (d m : ℤ) :
    dedekindSum (d + (D : ℤ) * m) D = dedekindSum d D := by
  have hQ : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold dedekindSum
  apply Finset.sum_congr rfl
  intro j _
  have he : (((d + (D : ℤ) * m : ℤ) : ℚ) * (j.val : ℚ)) / (D : ℚ) =
      (d : ℚ) * (j.val : ℚ) / (D : ℚ) + ((m * (j.val : ℤ) : ℤ) : ℚ) := by
    push_cast
    field_simp [hQ] <;> ring
  rw [he, sawtooth_int_translate]

def integralDiagonal (D : ℕ) (a d : ℤ) : ℝ :=
  ((a : ℝ) + (d : ℝ)) / (24 * (D : ℝ))

def scaledCrossDiagonal (D : ℕ) (a d : ℤ) : ℝ :=
  (((2 * (a : ℝ)) / 24) + (((d : ℝ) / 2) / 6)) / (2 * (D : ℝ))

theorem scaledCrossDiagonal_eq {D : ℕ} (hD : 0 < D) (a d : ℤ) :
    scaledCrossDiagonal D a d = integralDiagonal D a d := by
  have hR : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  unfold scaledCrossDiagonal integralDiagonal
  field_simp [hR] <;> ring

def explicitEta (D : ℕ) (a d : ℤ) : ℂ :=
  Complex.exp (periodCoefficient *
    ((integralDiagonal D a d - (dedekindSum d D : ℝ) / 2 - 1 / 8 : ℝ) : ℂ))

def etaAtS : ℂ :=
  Complex.exp (periodCoefficient * ((-(1 / 8 : ℝ)) : ℂ))

theorem explicitEta_at_S : explicitEta 1 0 0 = etaAtS := by
  have hd : dedekindSum 0 1 = 0 := by
    norm_num [dedekindSum, Fin.sum_univ_one, Paper8ContourResidueWeights.sawtooth]
  simp [explicitEta, integralDiagonal, etaAtS, hd]

def crossEntry (D : ℕ) (a d : ℤ) : ℂ :=
  (chiFour (D : ZMod 4) : ℂ) *
    ((starRingEnd ℂ) (explicitEta D a d / etaAtS) *
      Complex.exp (periodCoefficient * (scaledCrossDiagonal D a d : ℂ)))

private theorem crossEntry_eq {D : ℕ} (hD : 0 < D) (a d : ℤ) :
    crossEntry D a d = (chiFour (D : ZMod 4) : ℂ) * referenceEntry D d := by
  unfold crossEntry explicitEta etaAtS referenceEntry
  rw [scaledCrossDiagonal_eq hD, ← Complex.exp_sub, ← Complex.exp_conj, ← Complex.exp_add]
  congr 2
  simp only [periodCoefficient, map_sub, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  simp only [map_div₀, map_neg, map_one, map_ofNat]
  ring

theorem translated_crossEntry_eq {D : ℕ} (hD : 0 < D) (a d m : ℤ) :
    crossEntry D a (d + (D : ℤ) * m) =
      (chiFour (D : ZMod 4) : ℂ) * referenceEntry D d := by
  rw [crossEntry_eq hD, referenceEntry, referenceEntry, dedekind_translate hD]

end
end ManuscriptAudit.Paper8OddCrossCuspPhase

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper8OddCrossCuspPhase.dedekind_translate,
      ``ManuscriptAudit.Paper8OddCrossCuspPhase.scaledCrossDiagonal_eq,
      ``ManuscriptAudit.Paper8OddCrossCuspPhase.explicitEta_at_S,
      ``ManuscriptAudit.Paper8OddCrossCuspPhase.translated_crossEntry_eq] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
