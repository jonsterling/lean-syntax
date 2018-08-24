import category_theory.category

inductive bwd (α : Type) : Type
| emp {} : bwd
| snoc : bwd → α → bwd

notation `ε` := @bwd.emp _
infixl `≪`:5 := @bwd.snoc _
notation `⟪` l:(foldl `, ` (h t, (t ≪ h)) ε `⟫`) := l

@[simp]
def append {α} : bwd α → list α → bwd α
| xs [] := xs
| xs (y :: ys) := append (xs ≪ y) ys

infixl `⋉`:3 := append



def fam (α : Type) := α → Type


def valence (sort : Type) := list sort × sort
def arity (sort : Type) := bwd (valence sort) × sort


def sig (sort : Type) :=
fam (arity sort)


/-- Thinnings -/
inductive thn {sort} : bwd sort → bwd sort → Type
| emp {} : thn ⟪⟫ ⟪⟫
| cong {Γ Δ τ} : thn Γ Δ → thn (Γ ≪ τ) (Δ ≪ τ)
| drop {Γ Δ τ} : thn Γ Δ → thn (Γ ≪ τ) Δ

infixr `⇾`:30 := @thn _
infixl `≤` := @thn _

def idn {α} : Π (Γ : bwd α), Γ ⇾ Γ
| bwd.emp := thn.emp
| (bwd.snoc Γ _) := thn.cong (idn Γ)

def seq {α} : Π {Γ Δ Ξ : bwd α}, Γ ⇾ Δ → Δ ⇾ Ξ → Γ ⇾ Ξ
| _ _ _ thn.emp thn.emp := thn.emp
| _ _ _ (thn.cong δ) (thn.cong ξ) := thn.cong (seq δ ξ)
| _ _ _ (thn.cong δ) (thn.drop ξ) := thn.drop (seq δ ξ)
| _ _ _ (thn.drop δ) ξ := thn.drop (seq δ ξ)

theorem seq_left_idn {α} : Π {Γ Δ : bwd α} (γ : Δ ⇾ Γ), seq (idn _) γ = γ
| _ _ thn.emp := by refl
| _ _ (thn.cong ξ) :=
  begin
    unfold idn seq,
    rewrite (seq_left_idn ξ)
  end
| _ _ (thn.drop ξ) :=
  begin
    unfold idn seq,
    rewrite (seq_left_idn ξ)
  end


section
  variable sort : Type
  variable 𝔖 : sig sort

  /-- the clone (type of terms) and type of metasubstitutions -/
  mutual inductive cn, msb
  with cn : bwd sort → sort → Type
  | var {Γ τ} : Γ ⇾ ⟪τ⟫ → cn Γ τ
  | app {Γ 𝔛 τ} : 𝔖 (𝔛, τ) → msb Γ 𝔛 → cn Γ τ
  with msb : bwd sort → bwd (valence sort) → Type
  | emp {Γ} : msb Γ ⟪⟫
  | snoc {Γ 𝔛 Δ τ} : msb Γ 𝔛 → cn (Γ ⋉ Δ) τ → msb Γ (𝔛 ≪ (Δ, τ))
end


namespace lambda_calculus
  inductive sort : Type
  | chk
  | syn

  open sort

  infixl `▶`:3 := prod.mk

  inductive LAM : arity sort → Type
  | lam : LAM (⟪[syn] ▶ chk⟫ ▶ chk)
  | app : LAM (⟪[] ▶ syn, [] ▶ chk⟫ ▶ syn)
  | up : LAM (⟪[] ▶ syn⟫ ▶ chk)

  infix `∙`:5 := cn.app
  notation `⦃` l:(foldl `, ` (h t, (msb.snoc t h)) (msb.emp _) `⦄`) := l

  notation `ƛ` t := LAM.lam ∙ ⦃ t ⦄
  notation `#` ξ := cn.var _ ξ
  notation `⇑` t := LAM.up ∙ ⦃ t ⦄
  notation `x₀` := thn.cong thn.emp

  def tm (Γ : bwd sort) := cn _ LAM Γ chk

  -- identity function
  example : tm ⟪⟫ :=
    ƛ ⇑ # x₀

end lambda_calculus
