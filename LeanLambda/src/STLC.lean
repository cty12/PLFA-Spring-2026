-- Extrinsically typed STLC with de Bruijn indices
namespace STLC

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

def single_subst (N : Raw) (M : Raw) : Raw :=
  let σ : Nat → Raw
    | 0     => M
    | i + 1 => .var i
  subst σ N

-------------------------------------------------------------------------------
-- 3. TYPING RELATION (Defined in Type for constructivity)
-------------------------------------------------------------------------------

abbrev Context := List Ty

inductive HasTypeVar : Context → Nat → Ty → Type where
  | Z : ∀ {Γ A}, HasTypeVar (A :: Γ) 0 A
  | S : ∀ {Γ A B i}, HasTypeVar Γ i A → HasTypeVar (B :: Γ) (i + 1) A

inductive HasType : Context → Raw → Ty → Type where
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

inductive Value : Raw → Type where
  | v_lam  : ∀ {A N}, Value (.lam A N)
  | v_zero : Value .zero
  | v_suc  : ∀ {V}, Value V → Value (.suc V)

inductive Step : Raw → Raw → Type where
  | xi_app1 : ∀ {L L' M}, Step L L' → Step (.app L M) (.app L' M)
  | xi_app2 : ∀ {V M M'}, Value V → Step M M' → Step (.app V M) (.app V M')
  | β_lam   : ∀ {A N W}, Value W → Step (.app (.lam A N) W) (single_subst N W)
  | xi_suc  : ∀ {M M'}, Step M M' → Step (.suc M) (.suc M')
  | xi_case : ∀ {L L' M N}, Step L L' → Step (.case L M N) (.case L' M N)
  | β_zero  : ∀ {M N}, Step (.case .zero M N) M
  | β_suc   : ∀ {V M N}, Value V → Step (.case (.suc V) M N) (single_subst N V)
  | β_mu    : ∀ {A N}, Step (.mu A N) (single_subst N (.mu A N))

infix:20 " —→ " => Step

-------------------------------------------------------------------------------
-- 5. STRUCTURAL LEMMAS
-------------------------------------------------------------------------------

def typing_rename {Γ Δ : Context} {ρ : Nat → Nat} {M : Raw} {A : Ty}
  (hρ : ∀ {i B}, HasTypeVar Γ i B → HasTypeVar Δ (ρ i) B)
  (hM : HasType Γ M A) : HasType Δ (rename ρ M) A :=
  match hM with
  | .t_var hV => .t_var (hρ hV)
  | .t_lam (A := A) (B := B) hN =>
      let hρ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasTypeVar (A :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_lam (typing_rename hρ' hN)
  | .t_app hL hM => .t_app (typing_rename hρ hL) (typing_rename hρ hM)
  | .t_zero => .t_zero
  | .t_suc hM => .t_suc (typing_rename hρ hM)
  | .t_case (A := A) hL hM hN =>
      let hρ' : ∀ {i C}, HasTypeVar (Ty.nat :: Γ) i C →
                        HasTypeVar (Ty.nat :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_case (typing_rename hρ hL) (typing_rename hρ hM) (typing_rename hρ' hN)
  | .t_mu (A := A) hN =>
      let hρ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasTypeVar (A :: Δ) (ext ρ i) C :=
        fun hV => match hV with
          | .Z => .Z
          | .S hV' => .S (hρ hV')
      .t_mu (typing_rename hρ' hN)

def typing_subst {Γ Δ : Context} {σ : Nat → Raw} {M : Raw} {A : Ty}
  (hσ : ∀ {i B}, HasTypeVar Γ i B → HasType Δ (σ i) B)
  (hM : HasType Γ M A) : HasType Δ (subst σ M) A :=
  match hM with
  | .t_var hV => hσ hV
  | .t_lam (A := A) (B := B) hN =>
      let hσ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasType (A :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              -- We use an explicit lambda for the renaming map
              typing_rename (Δ := A :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_lam (typing_subst hσ' hN)
  | .t_app hL hR => .t_app (typing_subst hσ hL) (typing_subst hσ hR)
  | .t_zero => .t_zero
  | .t_suc hK => .t_suc (typing_subst hσ hK)
  | .t_case (A := A) hL hM hN =>
      let hσ' : ∀ {i C}, HasTypeVar (Ty.nat :: Γ) i C →
                        HasType (Ty.nat :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              typing_rename (Δ := Ty.nat :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_case (typing_subst hσ hL) (typing_subst hσ hM) (typing_subst hσ' hN)
  | .t_mu (A := A) hN =>
      let hσ' : ∀ {i C}, HasTypeVar (A :: Γ) i C →
                        HasType (A :: Δ) (exts σ i) C :=
        fun hV => match hV with
          | .Z => .t_var .Z
          | .S v =>
              typing_rename (Δ := A :: Δ) (ρ := Nat.succ)
                (fun hVar => .S (hσ v |> fun _ => hVar)) (hσ v)
      .t_mu (typing_subst hσ' hN)

def typing_single_subst {Γ : Context} {A B : Ty} {N M : Raw}
  (hN : HasType (B :: Γ) N A) (hM : HasType Γ M B) :
  HasType Γ (single_subst N M) A := by
  -- Define the mapping: 0 goes to M, and j+1 shifts down to j
  let σ := fun (i : Nat) => match i with | 0 => M | j+1 => .var j

  -- Apply the substitution lemma
  refine typing_subst (Δ := Γ) (σ := σ) ?_ hN

  -- Prove the substitution is well-typed for all variables
  intro i C hVar
  cases hVar with
  | Z =>
    -- Case i = 0: σ(0) = M. We know Γ ⊢ M : B from hM.
    exact hM
  | S hVar' =>
    -- Case i = j+1: σ(j+1) = var j.
    -- Since the context was (B :: Γ), index j+1 had type C.
    -- Therefore, in Γ, index j has type C.
    exact .t_var hVar'

-------------------------------------------------------------------------------
-- 6. PROGRESS & PRESERVATION
-------------------------------------------------------------------------------

def preservation {M N : Raw} {A : Ty}
  (hT : HasType [] M A) (hS : M —→ N) : HasType [] N A :=
  match hS with
  | .β_lam hV =>
      match hT with
      | .t_app (.t_lam hN) hM => typing_single_subst hN hM
  | .β_zero =>
      match hT with
      | .t_case _ hM _ => hM
  | .β_suc hV =>
      match hT with
      | .t_case (.t_suc hL) _ hN => typing_single_subst hN hL
  | .β_mu (A := ATy) (N := Body) =>
      match hT with
      | .t_mu hN => typing_single_subst hN (.t_mu hN)
  | .xi_app1 s =>
      match hT with
      | .t_app hL hM => .t_app (preservation hL s) hM
  | .xi_app2 v s =>
      match hT with
      | .t_app hL hM => .t_app hL (preservation hM s)
  | .xi_suc s =>
      match hT with
      | .t_suc hM => .t_suc (preservation hM s)
  | .xi_case s =>
      match hT with
      | .t_case hL hM hN => .t_case (preservation hL s) hM hN

inductive ProgressResult (M : Raw) where
  | step : ∀ {N}, (M —→ N) → ProgressResult M
  | done : Value M → ProgressResult M

def progress {Γ : Context} {M : Raw} {A : Ty} (h : HasType Γ M A) :
  Γ = [] → ProgressResult M := fun hEmpty =>
  match Γ, M, A, h with
  | _, .var i, _, .t_var hV => by subst hEmpty; nomatch hV
  | _, .lam A N, _, .t_lam hN => .done .v_lam
  | _, .app L M, B, .t_app hL hM =>
      match progress hL hEmpty, progress hM hEmpty with
      | .step s, _ => .step (.xi_app1 s)
      | .done vL, .step s => .step (.xi_app2 vL s)
      | .done vL, .done vM => match L, vL with | .lam _ _, .v_lam => .step (.β_lam vM)
  | _, .zero, _, .t_zero => .done .v_zero
  | _, .suc M, _, .t_suc hM =>
      match progress hM hEmpty with | .step s => .step (.xi_suc s) | .done v => .done (.v_suc v)
  | _, .case L M N, A, .t_case hL hM hN =>
      match progress hL hEmpty with
      | .step s => .step (.xi_case s)
      | .done vL => match L, vL with
          | .zero, .v_zero => .step .β_zero
          | .suc _, .v_suc v => .step (.β_suc v)
  | _, .mu A N, _, .t_mu hN => .step .β_mu

def progress_top {M : Raw} {A : Ty} (h : HasType [] M A) : ProgressResult M :=
  progress h rfl

-- Ported from Agda: lecture-notes-Substitution

-------------------------------------------------------------------------------
-- 1. SIGMA-CALCULUS DEFINITIONS
-------------------------------------------------------------------------------

/-- Substitution sequencing (σ ⨟ τ): Applying τ to the result of σ -/
def seq (σ₁ : Nat → Raw) (σ₂ : Nat → Raw) : Nat → Raw :=
  fun i => subst σ₂ (σ₁ i)

infixr:50 " ⨟ " => seq

/-- Substitution for single term at index 1: N 〔 M 〕 -/
def subst_one_at_one (N : Raw) (M : Raw) : Raw :=
  subst (exts (fun i => match i with | 0 => M | j+1 => .var j)) N

-------------------------------------------------------------------------------
-- 2. CORE SUBSTITUTION THEOREMS
-------------------------------------------------------------------------------

/-- rename ρ₂ (rename ρ₁ M) ≡ rename (ρ₂ ∘ ρ₁) M -/
theorem rename_rename_commute (ρ₁ ρ₂ : Nat → Nat) (M : Raw) :
  rename ρ₂ (rename ρ₁ M) = rename (fun i => ρ₂ (ρ₁ i)) M := by
  induction M generalizing ρ₁ ρ₂
  case var i => rfl
  case lam A N ih =>
    simp [rename]
    rw [ih (ext ρ₁) (ext ρ₂)]
    have ext_comp : (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
      funext i; cases i; rfl
    congr; exact ext_comp
  case app L M ihL ihM => simp [rename]; rw [ihL, ihM]
  case zero => rfl
  case suc M ih => simp [rename]; rw [ih]
  case case L M N ihL ihM ihN =>
    simp [rename]; rw [ihL, ihM]
    rw [ihN (ext ρ₁) (ext ρ₂)]
    have ext_comp : (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
      funext i; cases i; rfl
    congr; exact ext_comp
  case mu A N ih =>
    simp [rename]; rw [ih (ext ρ₁) (ext ρ₂)]
    have ext_comp : (fun i => ext ρ₂ (ext ρ₁ i)) = ext (fun i => ρ₂ (ρ₁ i)) := by
      funext i; cases i; rfl
    congr; exact ext_comp

/-- subst τ (rename ρ M) ≡ subst (τ ∘ ρ) M -/
theorem rename_subst_commute (ρ : Nat → Nat) (τ : Nat → Raw) (M : Raw) :
  subst τ (rename ρ M) = subst (fun i => τ (ρ i)) M := by
  induction M generalizing ρ τ with
  | var i => rfl
  | lam A N ih =>
    simp [rename, subst, exts]
    rw [ih (ext ρ) (exts τ)]
    congr; funext i; cases i with
    | zero => rfl
    | succ j => simp [ext, exts, rename_rename_commute]
  | app L M ihL ihM => simp [rename, subst]; rw [ihL, ihM]
  | zero => rfl
  | suc M ih => simp [rename, subst]; rw [ih]
  | case L M N ihL ihM ihN =>
    simp [rename, subst]; rw [ihL, ihM, ihN (ext ρ) (exts τ)]
    congr; funext i; cases i <;> simp [ext, exts, rename_rename_commute]
  | mu A N ih =>
    simp [rename, subst]; rw [ih (ext ρ) (exts τ)]
    congr; funext i; cases i <;> simp [ext, exts, rename_rename_commute]

/-- subst τ (subst σ M) ≡ subst (σ ⨟ τ) M -/
theorem sub_sub (σ τ : Nat → Raw) (M : Raw) :
  subst τ (subst σ M) = subst (σ ⨟ τ) M := by
  induction M generalizing σ τ with
  | var i => rfl
  | lam A N ih =>
    simp [subst, exts]
    rw [ih (exts σ) (exts τ)]
    congr; funext i; cases i with
    | zero => rfl
    | succ j => simp [exts, seq, rename_subst_commute]
  | app L M ihL ihM => simp [subst]; rw [ihL σ τ, ihM σ τ]
  | zero => rfl
  | suc M ih => simp [subst]; rw [ih σ τ]
  | case L M N ihL ihM ihN =>
    simp [subst]; rw [ihL σ τ, ihM σ τ, ihN (exts σ) (exts τ)]
    congr; funext i; cases i <;> simp [exts, seq, rename_subst_commute]
  | mu A N ih =>
    simp [subst]; rw [ih (exts σ) (exts τ)]
    congr; funext i; cases i <;> simp [exts, seq, rename_subst_commute]

-------------------------------------------------------------------------------
-- 3. FINAL AGDA THEOREMS
-------------------------------------------------------------------------------

/-- substitution : M [ N ] [ L ] ≡ M 〔 L 〕 [ N [ L ] ] -/
theorem substitution {M N L : Raw} :
  instantiate (instantiate M N) L = instantiate (subst_one_at_one M L) (instantiate N L) := by
  simp [instantiate, subst_one_at_one, sub_sub]
  congr
  funext i; cases i with
  | zero => rfl
  | succ j => cases j <;> rfl

/-- exts-sub-cons : (subst (exts σ) N) [ V ] ≡ subst (V • σ) N -/
theorem exts_sub_cons {σ : Nat → Raw} {N : Raw} {V : Raw} :
  instantiate (subst (exts σ) N) V = subst (fun i => match i with | 0 => V | j+1 => σ j) N := by
  simp [instantiate, sub_sub]
  congr
  funext i; cases i with
  | zero => rfl
  | succ j => simp [exts, seq, rename_subst_commute]

end STLC
