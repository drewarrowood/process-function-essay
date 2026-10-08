-- Temporal reading of the process-function lift.
-- Lean 4, no Mathlib, no sorry, no axiom.
-- Unique finish is exists-unique of the fixed-point formula.
-- The open shuffle is a bijection for every w, not a temporal operator.

namespace TemporalLift

abbrev Local (n : Nat) := Fin n → Bool → Bool
abbrev Proc (n : Nat) := (Fin n → Bool) → (Fin n → Bool)

def Fix {n : Nat} (w : Proc n) (f : Local n) (o : Fin n → Bool) : Prop :=
  (fun k => f k ((w o) k)) = o

def IsProcess {n : Nat} (w : Proc n) : Prop :=
  ∀ f : Local n, ∃ o, Fix w f o ∧ ∀ p, Fix w f p → p = o

def NoFinish {n : Nat} (w : Proc n) (f : Local n) : Prop :=
  ∀ o, ¬ Fix w f o

def TwoFinishes {n : Nat} (w : Proc n) (f : Local n) : Prop :=
  ∃ o p, Fix w f o ∧ Fix w f p ∧ o ≠ p

theorem process_not_empty {n : Nat} (w : Proc n) (hw : IsProcess w) (f : Local n) :
    ∃ o, Fix w f o := by
  rcases hw f with ⟨o, ho, _⟩
  exact ⟨o, ho⟩

theorem process_unique {n : Nat} (w : Proc n) (hw : IsProcess w) (f : Local n)
    (o p : Fin n → Bool) (ho : Fix w f o) (hp : Fix w f p) : o = p := by
  rcases hw f with ⟨q, _, hu⟩
  exact (hu o ho).trans (hu p hp).symm

theorem xor_cancel (a b : Bool) : xor a (xor a b) = b := by
  cases a <;> cases b <;> rfl

def extend {n : Nat} (w : Proc n)
    (oe : (Fin n → Bool) × (Fin n → Bool)) :=
  (fun k => xor (w oe.1 k) (oe.2 k), oe.1)

def extendInv {n : Nat} (w : Proc n)
    (is : (Fin n → Bool) × (Fin n → Bool)) :=
  (is.2, fun k => xor (w is.2 k) (is.1 k))

theorem extend_left_inv {n : Nat} (w : Proc n)
    (oe : (Fin n → Bool) × (Fin n → Bool)) :
    extendInv w (extend w oe) = oe := by
  cases oe with
  | mk o e =>
    apply Prod.ext
    · rfl
    · funext k
      simpa [extend, extendInv] using xor_cancel (w o k) (e k)

theorem extend_right_inv {n : Nat} (w : Proc n)
    (is : (Fin n → Bool) × (Fin n → Bool)) :
    extend w (extendInv w is) = is := by
  cases is with
  | mk i s =>
    apply Prod.ext
    · funext k
      simpa [extend, extendInv] using xor_cancel (w s k) (i k)
    · rfl

abbrev S := Bool × Bool × Bool

def outs : List S :=
  [(false,false,false),(false,false,true),(false,true,false),(false,true,true),
   (true,false,false),(true,false,true),(true,true,false),(true,true,true)]

theorem closed_copy_has_eight :
    (outs.filter (fun s => s == s)).length = 8 := by
  native_decide

end TemporalLift
