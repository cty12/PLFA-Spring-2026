-- Extrinsically typed STLC with de Bruijn indices
namespace Extrinsic

-------------------------------------------------------------------------------
-- 1. SYNTAX & TYPES
-------------------------------------------------------------------------------

inductive Ty where
  | nat : Ty
  | fn  : Ty → Ty → Ty
  deriving BEq

infixr:70 " ⇒ " => Ty.fn

inductive Raw where
  | var  : Nat → Raw
  | lam  : Ty → Raw → Raw
  | app  : Raw → Raw → Raw
  | zero : Raw
  | suc  : Raw → Raw
  | case : Raw → Raw → Raw → Raw
  | mu   : Ty → Raw → Raw

-------------------------------------------------------------------------------
-- 2. RENAMING & PARALLEL SUBSTITUTION
-------------------------------------------------------------------------------

-- Maps variables to variables (Lifting)
def ext (ρ : Nat → Nat) : Nat → Nat
  | 0     => 0
  | i + 1 => (ρ i) + 1

def rename (ρ : Nat → Nat) : Raw → Raw
  | .var i      => .var (ρ i)
  | .lam A N    => .lam A (rename (ext ρ) N)
  | .app L M    => .app (rename ρ L) (rename ρ M)
  | .zero       => .zero
  | .suc M      => .suc (rename ρ M)
  | .case L M N => .case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  | .mu A N     => .mu A (rename (ext ρ) N)

-- Maps variables to terms
def exts (σ : Nat → Raw) : Nat → Raw
  | 0     => .var 0
  | i + 1 => rename (Nat.succ) (σ i)

def subst (σ : Nat → Raw) : Raw → Raw
  | .var i      => σ i
  | .lam A N    => .lam A (subst (exts σ) N)
  | .app L M    => .app (subst σ L) (subst σ M)
  | .zero       => .zero
  | .suc M      => .suc (subst σ M)
  | .case L M N => .case (subst σ L) (subst σ M) (subst (exts σ) N)
  | .mu A N     => .mu A (subst (exts σ) N)

-- Single substitution: N [ 0 ↦ M ]
def instantiate (N : Raw) (M : Raw) : Raw :=
  let σ : Nat → Raw
    | 0     => M
    | i + 1 => .var i
  subst σ N

-------------------------------------------------------------------------------
-- 3. TYPING RELATION
-------------------------------------------------------------------------------

abbrev Context := List Ty

inductive HasTypeVar : Context → Nat → Ty → Prop where
  | Z : ∀ {Γ A}, HasTypeVar (A :: Γ) 0 A
  | S : ∀ {Γ A B i}, HasTypeVar Γ i A → HasTypeVar (B :: Γ) (i + 1) A

inductive HasType : Context → Raw → Ty → Prop where
  | t_var : ∀ {Γ i A},
      HasTypeVar Γ i A → HasType Γ (.var i) A
  | t_lam : ∀ {Γ A B N},
      HasType (A :: Γ) N B → HasType Γ (.lam A N) (A ⇒ B)
  | t_app : ∀ {Γ A B L M},
      HasType Γ L (A ⇒ B) → HasType Γ M A → HasType Γ (.app L M) B
  | t_zero : ∀ {Γ},
      HasType Γ .zero .nat
  | t_suc : ∀ {Γ M},
      HasType Γ M .nat → HasType Γ (.suc M) .nat
  | t_case : ∀ {Γ A L M N},
      HasType Γ L .nat → 
      HasType Γ M A → 
      HasType (.nat :: Γ) N A → 
      HasType Γ (.case L M N) A
  | t_mu : ∀ {Γ A N},
      HasType (A :: Γ) N A → HasType Γ (.mu A N) A

-------------------------------------------------------------------------------
-- 4. VALUES & REDUCTION
-------------------------------------------------------------------------------

inductive Value : Raw → Prop where
  | v_lam  : ∀ {A N}, Value (.lam A N)
  | v_zero : Value .zero
  | v_suc  : ∀ {V}, Value V → Value (.suc V)

inductive Step : Raw → Raw → Prop where
  | xi_app1 : ∀ {L L' M}, Step L L' → Step (.app L M) (.app L' M)
  | xi_app2 : ∀ {V M M'}, Value V → Step M M' → Step (.app V M) (.app V M')
  | β_lam   : ∀ {A N W}, Value W → Step (.app (.lam A N) W) (instantiate N W)
  | xi_suc  : ∀ {M M'}, Step M M' → Step (.suc M) (.suc M')
  | xi_case : ∀ {L L' M N}, Step L L' → Step (.case L M N) (.case L' M N)
  | β_zero  : ∀ {M N}, Step (.case .zero M N) M
  | β_suc   : ∀ {V M N}, Value V → Step (.case (.suc V) M N) (instantiate N V)
  | β_mu    : ∀ {A N}, Step (.mu A N) (instantiate N (.mu A N))

infix:20 " —→ " => Step

-------------------------------------------------------------------------------
-- 5. STRUCTURAL LEMMAS
-------------------------------------------------------------------------------

theorem typing_rename {Γ Δ : Context} {ρ : Nat → Nat} {M : Raw} {A : Ty}
  (hρ : ∀ {i B}, HasTypeVar Γ i B → HasTypeVar Δ (ρ i) B)
  (hM : HasType Γ M A) : HasType Δ (rename ρ M) A := by
  induction hM generalizing Δ ρ with
  | t_var hV => exact .t_var (hρ hV)
  | t_lam hN ih => 
    apply HasType.t_lam; apply ih
    intro i B hV; cases hV <;> constructor; exact hρ ‹_›
  | t_app hL hM ihL ihM => exact .t_app (ihL hρ) (ihM hρ)
  | t_zero => exact .t_zero
  | t_suc hM ih => exact .t_suc (ih hρ)
  | t_case hL hM hN ihL ihM ihN => 
    apply HasType.t_case (ihL hρ) (ihM hρ)
    apply ihN; intro i B hV; cases hV <;> constructor; exact hρ ‹_›
  | t_mu hN ih => 
    apply HasType.t_mu; apply ih
    intro i B hV; cases hV <;> constructor; exact hρ ‹_›

theorem typing_subst {Γ Δ : Context} {σ : Nat → Raw} {M : Raw} {A : Ty}
  (hσ : ∀ {i B}, HasTypeVar Γ i B → HasType Δ (σ i) B)
  (hM : HasType Γ M A) : HasType Δ (subst σ M) A := by
  induction hM generalizing Δ σ with
  | t_var hV => exact hσ hV
  | t_lam hN ih => 
    apply HasType.t_lam; apply ih; intro i B hV; cases hV
    · exact .t_var .Z
    · apply typing_rename (ρ := Nat.succ) (hρ := λ _ _ h => .S h)
      exact hσ ‹_›
  | t_app hL hM ihL ihM => exact .t_app (ihL hσ) (ihM hσ)
  | t_zero => exact .t_zero
  | t_suc hM ih => exact .t_suc (ih hσ)
  | t_case hL hM hN ihL ihM ihN => 
    apply HasType.t_case (ihL hσ) (ihM hσ); apply ihN; intro i B hV; cases hV
    · exact .t_var .Z
    · apply typing_rename (ρ := Nat.succ) (hρ := λ _ _ h => .S h)
      exact hσ ‹_›
  | t_mu hN ih => 
    apply HasType.t_mu; apply ih; intro i B hV; cases hV
    · exact .t_var .Z
    · apply typing_rename (ρ := Nat.succ) (hρ := λ _ _ h => .S h)
      exact hσ ‹_›

theorem typing_instantiation {Γ A B} {N M}
  (hN : HasType (B :: Γ) N A) (hM : HasType Γ M B) : 
  HasType Γ (instantiate N M) A := by
  apply typing_subst (σ := λ i => match i with | 0 => M | j+1 => .var j) hN
  intro i C hV; cases hV <;> (try exact hM); exact .t_var ‹_›

-------------------------------------------------------------------------------
-- 6. MAIN THEOREMS: PROGRESS & PRESERVATION
-------------------------------------------------------------------------------

theorem preservation {M N : Raw} {A : Ty}
  (hTyping : HasType [] M A) (hStep : M —→ N) : HasType [] N A := by
  induction hStep generalizing A with
  | β_lam hV => 
    cases hTyping with 
    | t_app hL hM => cases hL with | t_lam hN => exact typing_instantiation hN hM
  | β_zero => 
    cases hTyping with | t_case _ hM _ => exact hM
  | β_suc hV => 
    cases hTyping with 
    | t_case hL _ hN => cases hL with | t_suc hL' => 
      exact typing_instantiation hN hL'
  | β_mu => 
    cases hTyping with | t_mu hN => exact typing_instantiation hN hTyping
  | xi_app1 _ ih => 
    cases hTyping with | t_app hL hM => exact .t_app (ih hL) hM
  | xi_app2 _ _ ih => 
    cases hTyping with | t_app hL hM => exact .t_app hL (ih hM)
  | xi_suc _ ih => 
    cases hTyping with | t_suc hM => exact .t_suc (ih hM)
  | xi_case _ ih => 
    cases hTyping with | t_case hL hM hN => exact .t_case (ih hL) hM hN

inductive ProgressResult (M : Raw) where
  | step : ∀ {N}, (M —→ N) → ProgressResult M
  | done : Value M → ProgressResult M

theorem progress {M : Raw} {A : Ty} (h : HasType [] M A) : ProgressResult M := by
  induction h with
  | t_var hV => nomatch hV
  | t_lam => exact .done .v_lam
  | t_app _ _ ihL ihM => 
    match ihL with
    | .step hS => exact .step (.xi_app1 hS)
    | .done vL => match ihM with
      | .step hS => exact .step (.xi_app2 vL hS)
      | .done vM => cases vL; exact .step (.β_lam vM)
  | t_zero => exact .done .v_zero
  | t_suc _ ih => match ih with
    | .step hS => exact .step (.xi_suc hS)
    | .done vM => exact .done (.v_suc vM)
  | t_case _ _ _ ihL _ => match ihL with
    | .step hS => exact .step (.xi_case hS)
    | .done vL => cases vL with
      | v_zero => exact .step .β_zero
      | v_suc vL' => exact .step (.β_suc vL')
  | t_mu hN _ => exact .step .β_mu

end Extrinsic