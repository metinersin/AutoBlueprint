import Lean.Declaration

open Lean

-- instance : BEq ConstantInfo where
--   beq c1 c2 := c1.name == c2.name

def ConstantInfo.quickCmp (c₁ c₂ : ConstantInfo) : Ordering :=
  Name.quickCmp c₁.name c₂.name

def ConstantInfoSet := RBTree ConstantInfo ConstantInfo.quickCmp

namespace ConstantInfoSet --region

def empty : ConstantInfoSet := mkRBTree ConstantInfo ConstantInfo.quickCmp
instance : EmptyCollection ConstantInfoSet := ⟨empty⟩
instance : Inhabited ConstantInfoSet := ⟨empty⟩

instance : Coe ConstantInfoSet (RBTree ConstantInfo ConstantInfo.quickCmp) := ⟨id⟩

instance : ForIn m ConstantInfoSet ConstantInfo where
  forIn := RBTree.forIn

def contains (s : ConstantInfoSet) (c : ConstantInfo) : Bool := RBMap.contains s c

end ConstantInfoSet --end
