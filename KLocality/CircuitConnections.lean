import KLocality.Core
import Cslib.Computability.Circuits.Basis
import Cslib.Computability.Circuits.Circuit.Basic

namespace KLocality

universe u

/-!
Deterministic circuit-to-localization formalization aligned with the paper:

* `C_r(S)`: minimum size of a fan-in-`r` recognizer for support set `S`.
* `G_r(D)`: minimum `m + s` over fan-in-`r` generators with `m` random input bits
  and circuit size `s`.

The final upper-bound theorems are stated in a paper-shaped way:
if one supplies the local-verification reduction as a bridge hypothesis, then
`LC_k(D) ≤ G_{k-1}(D)` and (for flat-support constructions) `LC_k(D) ≤ C_{k-1}(S)`.
-/

open Cslib
open Cslib.Circuits

noncomputable def uniformInput (m : Nat) : Distribution (BitVec m) :=
  PMF.uniformOfFintype (BitVec m)

structure MultiOutputCircuit (Op : Type u) (m n : Nat) where
  gates : List (Gate Op)
  outputWire : Fin n → Nat

namespace MultiOutputCircuit

def size {Op : Type u} {m n : Nat} (C : MultiOutputCircuit Op m n) : Nat :=
  C.gates.length

def toSingle {Op : Type u} {m n : Nat} (C : MultiOutputCircuit Op m n) (i : Fin n) :
    Circuit Op m :=
  { gates := C.gates, outputWire := C.outputWire i }

def eval {Op : Type u} {m n : Nat} [Basis Op] (C : MultiOutputCircuit Op m n) :
    BitVec m → BitVec n :=
  fun input i => (C.toSingle i).eval input

end MultiOutputCircuit

/-- `C_r` recognizers for subsets of `{0,1}^n`. -/
def Recognizes (r n : Nat) (C : Circuit (BoundedFanInOp r) n) (S : Set (BitVec n)) : Prop :=
  ∀ x : BitVec n, x ∈ S ↔ C.eval x = true

def RecognizerWitness (r n : Nat) (S : Set (BitVec n)) (t : Nat) : Prop :=
  ∃ C : Circuit (BoundedFanInOp r) n, Recognizes r n C S ∧ C.size = t

/-- Paper-style `C_r(S)`: minimum circuit size among fan-in-`r` recognizers of `S`. -/
noncomputable def CComplexity (r n : Nat) (S : Set (BitVec n))
    (hExists : ∃ t, RecognizerWitness r n S t) : Nat := by
  classical
  exact Nat.find hExists

/-- Paper-notation alias `C_r(S)`. -/
noncomputable abbrev C_r (r n : Nat) (S : Set (BitVec n))
    (hExists : ∃ t, RecognizerWitness r n S t) : Nat :=
  CComplexity r n S hExists

theorem CComplexity_spec
    (r n : Nat) (S : Set (BitVec n))
    (hExists : ∃ t, RecognizerWitness r n S t) :
    RecognizerWitness r n S (CComplexity r n S hExists) := by
  classical
  exact Nat.find_spec hExists

theorem CComplexity_min
    (r n : Nat) (S : Set (BitVec n))
    (hExists : ∃ t, RecognizerWitness r n S t) :
    ∀ t, RecognizerWitness r n S t → CComplexity r n S hExists ≤ t := by
  classical
  intro t ht
  exact Nat.find_min' hExists ht

theorem CComplexity_le_of_recognizer
    {r n : Nat} {S : Set (BitVec n)}
    (hExists : ∃ t, RecognizerWitness r n S t)
    (C : Circuit (BoundedFanInOp r) n)
    (hRec : Recognizes r n C S) :
    CComplexity r n S hExists ≤ C.size := by
  exact CComplexity_min r n S hExists C.size ⟨C, hRec, rfl⟩

/-- A fan-in-`r` multi-output circuit with `m` random bits generates distribution `D`. -/
def Generates (r m n : Nat) (C : MultiOutputCircuit (BoundedFanInOp r) m n)
    (D : Distribution (BitVec n)) : Prop :=
  (uniformInput m).map C.eval = D

def GeneratorWitness (r n : Nat) (D : Distribution (BitVec n)) (t : Nat) : Prop :=
  ∃ m : Nat, ∃ C : MultiOutputCircuit (BoundedFanInOp r) m n,
    Generates r m n C D ∧ m + C.size = t

/-- Paper-style `G_r(D)`: minimum `m + s` among fan-in-`r` generators of `D`. -/
noncomputable def GComplexity (r n : Nat) (D : Distribution (BitVec n))
    (hExists : ∃ t, GeneratorWitness r n D t) : Nat := by
  classical
  exact Nat.find hExists

/-- Paper-notation alias `G_r(D)`. -/
noncomputable abbrev G_r (r n : Nat) (D : Distribution (BitVec n))
    (hExists : ∃ t, GeneratorWitness r n D t) : Nat :=
  GComplexity r n D hExists

theorem GComplexity_spec
    (r n : Nat) (D : Distribution (BitVec n))
    (hExists : ∃ t, GeneratorWitness r n D t) :
    GeneratorWitness r n D (GComplexity r n D hExists) := by
  classical
  exact Nat.find_spec hExists

theorem GComplexity_min
    (r n : Nat) (D : Distribution (BitVec n))
    (hExists : ∃ t, GeneratorWitness r n D t) :
    ∀ t, GeneratorWitness r n D t → GComplexity r n D hExists ≤ t := by
  classical
  intro t ht
  exact Nat.find_min' hExists ht

theorem GComplexity_le_of_generator
    {r n m : Nat} {D : Distribution (BitVec n)}
    (hExists : ∃ t, GeneratorWitness r n D t)
    (C : MultiOutputCircuit (BoundedFanInOp r) m n)
    (hGen : Generates r m n C D) :
    GComplexity r n D hExists ≤ m + C.size := by
  exact GComplexity_min r n D hExists (m + C.size) ⟨m, C, hGen, rfl⟩

/-- Bridge assumption corresponding to the paper's generator reduction:
every fan-in-`r` generator yields an explicit local-verification witness with
latent count `m + size(C)`. -/
def GeneratorToLocalizationBridge (k r n : Nat) (D : Distribution (BitVec n)) : Prop :=
  ∀ (m : Nat) (C : MultiOutputCircuit (BoundedFanInOp r) m n),
    Generates r m n C D →
      Nonempty (LocalVerificationWitness k (Fin n) (Fin (m + C.size)) D)

/-- Bridge assumption corresponding to the paper's flat-support reduction:
every fan-in-`r` recognizer of `S` yields an explicit local-verification witness
with latent count equal to recognizer gate count. -/
def FlatRecognizerToLocalizationBridge (k r n : Nat)
    (S : Set (BitVec n)) (D : Distribution (BitVec n)) : Prop :=
  ∀ (C : Circuit (BoundedFanInOp r) n),
    Recognizes r n C S →
      Nonempty (LocalVerificationWitness k (Fin n) (Fin C.size) D)

/-- Paper-shaped upper bound: `LC_k(D) ≤ G_r(D)` from a generator-to-localization bridge. -/
theorem localizationComplexity_le_GComplexity
    {k r n : Nat} {D : Distribution (BitVec n)}
    (hLocExists : ∃ m, HasKLocalizationBits k m n D)
    (hGenExists : ∃ t, GeneratorWitness r n D t)
    (hBridge : GeneratorToLocalizationBridge k r n D) :
    localizationComplexityBits k n D hLocExists ≤ GComplexity r n D hGenExists := by
  have hSpec : GeneratorWitness r n D (GComplexity r n D hGenExists) :=
    GComplexity_spec r n D hGenExists
  rcases hSpec with ⟨m, C, hGen, hCost⟩
  rcases hBridge m C hGen with ⟨hWitness⟩
  have hLoc : HasKLocalizationBits k (m + C.size) n D :=
    hasKLocalizationBits_of_localVerificationWitness hWitness
  have hMin :=
    localizationComplexityBits_min k n D hLocExists (m + C.size) hLoc
  simpa [hCost] using hMin

/-- Paper-shaped upper bound: `LC_k(D) ≤ C_r(S)` from a flat-support localization bridge. -/
theorem localizationComplexity_le_CComplexity_of_flat_bridge
    {k r n : Nat} {S : Set (BitVec n)} {D : Distribution (BitVec n)}
    (hLocExists : ∃ m, HasKLocalizationBits k m n D)
    (hRecExists : ∃ t, RecognizerWitness r n S t)
    (hBridge : FlatRecognizerToLocalizationBridge k r n S D) :
    localizationComplexityBits k n D hLocExists ≤ CComplexity r n S hRecExists := by
  have hSpec : RecognizerWitness r n S (CComplexity r n S hRecExists) :=
    CComplexity_spec r n S hRecExists
  rcases hSpec with ⟨C, hRec, hSize⟩
  rcases hBridge C hRec with ⟨hWitness⟩
  have hLoc : HasKLocalizationBits k C.size n D :=
    hasKLocalizationBits_of_localVerificationWitness hWitness
  have hMin := localizationComplexityBits_min k n D hLocExists C.size hLoc
  have hRight : C.gates.length ≤ CComplexity r n S hRecExists := by
    simpa [Cslib.Circuits.Circuit.size] using (Nat.le_of_eq hSize)
  exact Nat.le_trans hMin hRight

/-- Paper-notation alias for `LC_k(D) ≤ G_r(D)`. -/
theorem LC_k_le_G_r
    {k r n : Nat} {D : Distribution (BitVec n)}
    (hLocExists : ∃ m, HasKLocalizationBits k m n D)
    (hGenExists : ∃ t, GeneratorWitness r n D t)
    (hBridge : GeneratorToLocalizationBridge k r n D) :
    LC_k k n D hLocExists ≤ G_r r n D hGenExists :=
  localizationComplexity_le_GComplexity hLocExists hGenExists hBridge

/-- Paper-notation alias for `LC_k(D) ≤ C_r(S)` in the flat-support setting. -/
theorem LC_k_le_C_r_of_flat
    {k r n : Nat} {S : Set (BitVec n)} {D : Distribution (BitVec n)}
    (hLocExists : ∃ m, HasKLocalizationBits k m n D)
    (hRecExists : ∃ t, RecognizerWitness r n S t)
    (hBridge : FlatRecognizerToLocalizationBridge k r n S D) :
    LC_k k n D hLocExists ≤ C_r r n S hRecExists :=
  localizationComplexity_le_CComplexity_of_flat_bridge hLocExists hRecExists hBridge

end KLocality
