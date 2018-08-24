import category_theory.category

inductive bwd (α : Type) : Type
| emp {} : bwd
| snoc : bwd → α → bwd

notation `ε` := @bwd.emp _
infixl `≪`:5 := @bwd.snoc _
notation `⟪` l:(foldl `, ` (h t, (t ≪ h)) ε `⟫`) := l

def append {α} : bwd α → list α → bwd α
| xs [] := xs
| xs (y :: ys) := append (xs ≪ y) ys

infixl `⋉`:3 := append



def fam (α : Type) := α → Type


def valence (sort : Type) := list sort × sort
def arity (sort : Type) := bwd (valence sort) × sort


def sig (sort : Type) :=
fam (arity sort)

infixl `▶`:2 := (λ x y, (x, y))


/-- Thinnings -/
inductive thn {sort} : bwd sort → bwd sort → Type
| emp {} : thn ⟪⟫ ⟪⟫
| cong {Γ Δ τ} : thn Γ Δ → thn (Γ ≪ τ) (Δ ≪ τ)
| drop {Γ Δ τ} : thn Γ Δ → thn (Γ ≪ τ) Δ

infixr `⇾`:30 := @thn _
infixl `≤` := @thn _

/- here's something the pattern compiler chokes on. -/
def idn {sort} : Π (Γ : bwd sort), Γ ⇾ Γ :=
begin
  intro Γ,
  induction Γ with _ _ ih,
  apply thn.emp,
  apply thn.cong,
  exact ih
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
  | emp {Γ} :msb Γ ⟪⟫
  | snoc {Γ 𝔛 Δ τ} : msb Γ 𝔛 → cn (Γ ⋉ Δ) τ → msb Γ (𝔛 ≪ (Δ, τ))

end
