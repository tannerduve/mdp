import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

open MeasureTheory
open CategoryTheory
open CategoryTheory.Limits

structure MarkovDecisionProcess (s : Type u) [MeasurableSpace s] (a : Type v) where
  ψ : a → s
  T : a → ProbabilityMeasure s

structure MDPCat : Type (max u v + 1) where
  (s : Type u)
  [ms : MeasurableSpace s]
  (a : Type v)
  [mdp : MarkovDecisionProcess s a]

instance (Y : MDPCat) : MeasurableSpace Y.s := Y.ms

structure MDP_morphism (X Y : MDPCat) where
(f : X.s → Y.s)
(meas_f : @Measurable X.s Y.s X.ms Y.ms f)
(g : X.a → Y.a)
(comm_ψ : ∀ (x : X.a), Y.mdp.ψ (g x) = f (X.mdp.ψ x))
(comm_T : ∀ (x : X.a), Y.mdp.T (g x) = Measure.map f (X.mdp.T x))

instance : Category MDPCat where
  Hom X Y := {(f, g) : (X.s → Y.s) × (X.a → Y.a) | @Measurable X.s Y.s X.ms Y.ms f }
  id X := ⟨(id, id), measurable_id⟩
  comp f g := ⟨(g.val.1 ∘ f.val.1, g.val.2 ∘ f.val.2), Measurable.comp g.property f.property⟩
  id_comp := by
      intros X Y f
      apply Subtype.ext
      dsimp
  comp_id := by
    intros X Y f
    apply Subtype.ext
    dsimp
  assoc := by
    intros W X Y Z f g h
    apply Subtype.ext
    dsimp
    rfl

def isSubprocess (X : MDPCat) (Y : MDPCat) : Prop :=
∃ φ : X ⟶ Y, Function.Injective φ.val.1 ∧ Function.Injective φ.val.2

def subprocess (X : MDPCat) (Y : MDPCat) (φ : X ⟶ Y) : Prop := Function.Injective φ.val.1 ∧
Function.Injective φ.val.2

theorem subprocess_factors {M₁ M₂ M : MDPCat} (f : M₁ ⟶ M₂)
(g : M ⟶ M₂) (h₁ : subprocess M₁ M₂ f) (h₂ : subprocess M M₂ g) :
  ∃! f' : M ⟶ M₁, f' ≫ f = g := by
  sorry
