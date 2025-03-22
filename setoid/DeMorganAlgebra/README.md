-- standard-library/src/Algebra/Lattice/Bundles.agda
record DeMorganAlgebra c ℓ : Set (suc (c ⊔ ℓ)) where
  infix  8 ¬_
  infixr 7 _∧_
  infixr 6 _∨_
  infix  4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    _∨_              : Op₂ Carrier
    _∧_              : Op₂ Carrier
    ¬_               : Op₁ Carrier
    ⊤                : Carrier
    ⊥                : Carrier
    isDeMorganAlgebra : IsDeMorganAlgebra _≈_ _∨_ _∧_ ¬_ ⊤ ⊥

  open IsDeMorganAlgebra isDeMorganAlgebra public

  distributiveLattice : DistributiveLattice _ _
  distributiveLattice = record
    { isDistributiveLattice = isDistributiveLattice
    }

  open DistributiveLattice distributiveLattice public
    using
    ( _≉_; setoid; rawLattice
    ; ∨-rawMagma; ∧-rawMagma
    ; lattice
    )


-- standard-library/src/Algebra/Lattice/Structures.agda
record IsDeMorganAlgebra (∨ ∧ : Op₂ A) (¬ : Op₁ A) (⊤ ⊥ : A) : Set (a ⊔ ℓ) where
  field
    isDistributiveLattice : IsDistributiveLattice ∨ ∧  
    -- 底层是一个分配格
    
    ¬-involution : Involutive ¬  
    -- 否定的双重否定等于自身: ¬(¬x) ≈ x
    
    ¬-cong : Congruent₁ ¬  
    -- 否定运算保持等价关系
    
    de-morgan₁ : DeMorgan₁ ¬ ∨ ∧
    -- 第一个德摩根律
    
    de-morgan₂ : DeMorgan₂ ¬ ∧ ∨
    -- 第二个德摩根律

--    ⊤-max : Maximum ⊤ ∧
--    ⊥-min : Minimum ⊥ ∨
    -- 有界(也可认为 ⊥ ⊤ 分别是 ∨ 和 ∧ 的单位元)
    ⊤-∧-identity : RightIdentity ⊤ ∧
    ⊥-∨-identity : RightIdentity ⊥ ∨


  open IsDistributiveLattice isDistributiveLattice public
