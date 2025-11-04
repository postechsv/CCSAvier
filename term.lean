--   Formalizing (Unsorted) Maude Terms Lean 4
--
--   Authors: Byoungho Son, POSTECH, South Korea
--
--   © 2025. This work is a draft and is not currently licensed.
--   No permission is granted to copy, use, or distribute this file.

namespace Term
/-- A first-order signature: each symbol `f` has a finite arity. -/
structure Signature where
  Symbol : Type
  arity  : Symbol → Nat

/-- Terms over a signature `Σ` with variables from `X`. -/
inductive Term (sig : Signature) (X : Type) : Type where
  | var : X → Term sig X
  | op  : (f : sig.Symbol) →
          (Fin (sig.arity f) → Term sig X) →  -- children indexed by positions
          Term sig X
---deriving Repr

instance [Repr sig.Symbol] [Repr X] : Repr (Term sig X) where
  reprPrec t _ := "hello"
    -- let rec go : Term sig X → String
    --   | .var x     => s!"var {repr x}"
    --   | .op f args => "f"
    --     /-let kids :=
    --       (List.finRange (sig.arity f)).map (fun i => go (args ⟨i, by
    --         have := List.mem_finRange.1 (by decide : i ∈ List.finRange _)
    --         simpa using this⟩))
    --     s!"op {repr f} [{String.intercalate ", " kids}]"-/
    -- .text (go t)


variable {sig : Signature} {X : Type}

/- Fold over terms -/
def fold {α : Sort _}
    (algVar : X → α)
    (algOp  : ∀ f : sig.Symbol, (Fin (sig.arity f) → α) → α)
    : Term sig X → α
  | Term.var x     => algVar x
  | Term.op f args => algOp f (fun i => fold algVar algOp (args i))

/- Variable Renaming -/
def rename {Y} (g : X → Y) : Term sig X → Term sig Y :=
  fold (fun x => Term.var (g x)) (fun f cs => Term.op f cs)

/- Substitution over Terms -/
def subst {Y} (σ : X → Term sig Y) : Term sig X → Term sig Y :=
  fold σ (fun f cs => Term.op f cs)

/- `Term Σ` is a free monad over the variables. -/
instance : Monad (Term sig) where
  pure := Term.var
  bind t σ := subst σ t

/- A Σ-algebra on a carrier `A`. -/
structure Algebra (sig : Signature) (A : Type) where
  (interp : ∀ f : sig.Symbol, (Fin (sig.arity f) → A) → A)

/- Evaluation function: homomorphic extension from `ρ : X → A` to the free monad. -/
def eval {A} (Aalg : Algebra sig A) (ρ : X → A) : Term sig X → A :=
  fold ρ (fun f cs => Aalg.interp f cs)


def Matches (t : Term sig X) (t' : Term sig Y) : Prop :=
  ∃ σ : X → Term sig Y, subst σ t = t'


-- Basic lemmas

/- Reflexivity (with same variable set): use the identity substitution. -/
-- theorem Matches.refl (t : Term sig X) : Matches t t :=
--   ⟨(fun x => Term.var x), by
     -- `subst (fun x => var x) t = t`
     -- follows from your `fold`-based definition
     -- (induction on `t` if needed)
     -- sketch:
    --  induction t with
    --  | var x      => rfl
    --  | op f args ih =>
    --        simp [subst, fold]
    --        funext i
    --        exact ih i

end Term



namespace TermExample
open Term

/- Some examples -/
inductive Sym | zero | succ | add
open Sym

def SigNat : Signature where
  Symbol := Sym
  arity
  | zero => 0
  | succ => 1
  | add  => 2

-- A sample term: add (succ x) zero
def xVar : Nat := 0

def t : Term SigNat Nat :=
  Term.op add
    (fun
      | ⟨0, _⟩ => Term.op succ (fun _ => Term.var xVar)
      | ⟨1, _⟩ => Term.op zero (fun i => nomatch i))
-- add (succ x) zero

-- #reduce t -- add (succ x) zero
-- #reduce --
-- #reduce (Term.subst (fun x => Term.var 42) t)
def t1 := (Term.subst (fun x => Term.var 42) t)

-- Interpret symbols in `Nat`
def NatAlg : Algebra SigNat Nat where
  interp
  | zero, _ => 0
  | succ, cs => Nat.succ (cs ⟨0, by decide⟩)
  | add,  cs => (cs ⟨0, by decide⟩) + (cs ⟨1, by decide⟩)

#eval eval NatAlg (fun x => x + 10) t  -- (succ (x+10)) + 0 = 11

end TermExample



namespace Pattern
open Term
--- Definition of Basic Patterns as pairs (Term, Prop)
structure BPat (sig : Signature) (X: Type) where
  term : Term sig X
  guard : Prop

--- Definition of Patterns as lists of Basic Patterns
abbrev Pattern (sig : Signature) (X: Type):= List (BPat sig X)
end Pattern


def plus (x y : Nat) := x + y
