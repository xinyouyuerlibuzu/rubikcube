import RubiksCube.RubiksCubeFunc
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.SpecificGroups.Alternating

open Equiv Perm
open Equiv Equiv.Perm Subgroup Fintype
open alternatingGroup
open BigOperators
-- set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

variable (α : Type*) [Fintype α] [DecidableEq α]
--本文件证明ValidCube和Reachable两个定义是等价的，由此可得到魔方随机拼装后可复原的概率是1/12

section ValidityChecks


  @[simp]
  lemma ft_valid --六个操作分别得到的x均是validcube
  : ∀x : RubiksSuperType,
  FaceTurn x → x ∈ ValidCube
  := by
    intro x hx
    cases hx with
    | _ =>
      simp only [ValidCube, U, D, R, L, F, B, U2, D2, R2, L2, F2, B2, U', D', R', L', F', B']
      -- 换句话说，就是代入计算的过程。
      decide

  /-- 举例：某个基本操作的复合，符合非直觉定义。 -/
  @[simp]
  lemma TPermValid : TPerm ∈ ValidCube :=
    by
      simp only [TPerm]
      repeat apply RubiksGroup.mul_mem' -- RubiksGroup.carrier就是ValidCube
      all_goals apply ft_valid -- 全部目标都使用上面的定理反推
      { apply FaceTurn.R } -- 这下面包括这行都是根据定义来的。
      { apply FaceTurn.U }
      { apply FaceTurn.R' }
      { apply FaceTurn.U' }
      { apply FaceTurn.R' }
      { apply FaceTurn.F }
      { apply FaceTurn.R2 }
      { apply FaceTurn.U' }
      { apply FaceTurn.R' }
      { apply FaceTurn.U' }
      { apply FaceTurn.R }
      { apply FaceTurn.U }
      { apply FaceTurn.R' }
      { apply FaceTurn.F' }
      done

  /-- 单个角块旋转了1次。不符合非直觉定义。 -/
  @[simp]
  lemma CornerTwistInvalid : CornerTwist ∉ ValidCube
  := by
      simp only [CornerTwist, ValidCube]
      simp only [Set.mem_setOf_eq]
      decide
      done
  /-- 单个棱块旋转了1次。不符合非直觉定义。 -/
  @[simp]
  lemma EdgeFlipInvalid : EdgeFlip ∉ ValidCube :=
    by
      simp only [EdgeFlip, ValidCube]
      decide
      done

end ValidityChecks


section RubikCube_BasicRule_2

  @[simp]
  lemma solved_reachable
  (x : RubiksSuperType)
  (h : x = Solved)
  : Reachable x
  := by
    rw [h]
    exact Reachable.Solved

  section rubikCubeFormula
  --下面定义各种特殊的状态变换操作
  --G1Perm:只改变两个角块的方向，分别+1/+2
  --G2Perm:只改变两个棱块的方向，分别+1/+1
  --G5Perm:只进行两个角块和两个棱块的2-循环
  --G4Perm:只进行三个角块的3-循环
  --G3Perm:只进行三个棱块的3-循环

  -- #eval R' * D * D * R -- 2↔8 5↔6
  -- #eval B' * U * U * B -- 2↔8 1↔4

    def G1Perm_element : RubiksSuperType
    := R' * D * D * R * B' * U * U * B -- 两个共轭的交换子。
    -- 1↔4 5↔6 2,3,7,8不变
  /-- g1:
  方向：UFR和DBL以外的块的方向不变。
  位置：UFR和DBL以外的块的位置不变。
  可以保持UFR和DBL以外的块的方向和位置，只改变UFR和DBL的方向，
  分别是UFR的方向数+2，DBL的方向数+1。 -/
  def G1Perm : RubiksSuperType -- R' D D R B' U U B R' D D R B' U U B
  := G1Perm_element^2
  -- #eval (F * G1Perm * F').1
  -- #eval (F * G1Perm * F').1.orient 7 -- 1
  -- #eval G1Perm
  --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 2, 0, 0, 0, 0, 0, 1] },
  --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
    def G2Perm_element1 : RubiksSuperType
    := L*F*R'*F'*L'
    def G2Perm_element2 : RubiksSuperType
    := U^2*R*U*R*U'*R^2*U^2
  /-- 可以保持其他块的方向和位置，只改变UF和UR的方向，分别是UF的方向+1，UR的方向的方向+1。-/
  def G2Perm : RubiksSuperType -- L F R' F' L' U2 R U R U' R2 U2 R
  --  L F R' F' L' U U R U R U' R R U U R
  := G2Perm_element1 * G2Perm_element2 * R
  def G2Perm_List:List RubiksSuperType := [L,F,R',F',L',U,U,R,U,R,U',R,R,U,U,R]
  -- #eval G2Perm
  --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

 -- 定义G2的“L,R,B”变式
    -- 先写3个映射，然后列表映射即可。
    def VariantFaceTurn_L : RubiksSuperType → RubiksSuperType :=
    fun x =>
      if x = U then U
      else if x = D then D
      else if x = R then F
      else if x = L then B
      else if x = F then L
      else if x = B then R
      else if x = U2 then U2
      else if x = D2 then D2
      else if x = R2 then F2
      else if x = L2 then B2
      else if x = F2 then L2
      else if x = B2 then R2
      else if x = U' then U'
      else if x = D' then D'
      else if x = R' then F'
      else if x = L' then B'
      else if x = F' then L'
      else if x = B' then R'
      else 1

    def VariantFaceTurn_R : RubiksSuperType → RubiksSuperType :=
    fun x =>
      if x = U then U
      else if x = D then D
      else if x = R then B
      else if x = L then F
      else if x = F then R
      else if x = B then L
      else if x = U2 then U2
      else if x = D2 then D2
      else if x = R2 then B2
      else if x = L2 then F2
      else if x = F2 then R2
      else if x = B2 then L2
      else if x = U' then U'
      else if x = D' then D'
      else if x = R' then B'
      else if x = L' then F'
      else if x = F' then R'
      else if x = B' then L'
      else 1

    def VariantFaceTurn_B : RubiksSuperType → RubiksSuperType :=
    fun x =>
      if x = U then U
      else if x = D then D
      else if x = R then L
      else if x = L then R
      else if x = F then B
      else if x = B then F
      else if x = U2 then U2
      else if x = D2 then D2
      else if x = R2 then L2
      else if x = L2 then R2
      else if x = F2 then B2
      else if x = B2 then F2
      else if x = U' then U'
      else if x = D' then D'
      else if x = R' then L'
      else if x = L' then R'
      else if x = F' then B'
      else if x = B' then F'
      else 1

    def testG1Perm_L : List RubiksSuperType := [R' ,D ,D ,R ,B' ,U ,U ,B,R' ,D ,D ,R ,B' ,U ,U ,B]
    def VariantFaceTurn_L_List : (l:List RubiksSuperType) → RubiksSuperType
    := fun l => (l.map VariantFaceTurn_L).prod
    -- #eval VariantFaceTurn_L_List testG1Perm_L
    -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 1, 0] },
    -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
    def VariantFaceTurn_R_List : (l:List RubiksSuperType) → RubiksSuperType
    := fun l => (l.map VariantFaceTurn_R).prod
    def VariantFaceTurn_B_List : (l:List RubiksSuperType) → RubiksSuperType
    := fun l => (l.map VariantFaceTurn_B).prod

    abbrev VarL := VariantFaceTurn_L_List
    abbrev VarR := VariantFaceTurn_R_List
    abbrev VarB := VariantFaceTurn_B_List


    #eval VariantFaceTurn_R_List G2Perm_List

  def G5Perm_element1 : RubiksSuperType
  := R*U*R'*U'*R'*F*R*R*U'*R'
  /-- 是2个2循环:2个角块的2循环+2个棱块的2循环,详细: 角块ρ(g5) =(2,3)， 棱块σ(g5) =(1,2) -/
  def G5Perm : RubiksSuperType -- R U R' F' R U R' U' R' F R R U' R' U'
  := R*U*R'*F'*G5Perm_element1*U'
  -- #eval G5Perm
  -- ({ permute := ![0, 2, 1, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  -- { permute := ![1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  /-- 是一个角块3循环 ρ(g4) =(2,4,3) 这里指绝对位置2的块的新位置是绝对位置4；相当于顺时针 -/
  def G4Perm : RubiksSuperType -- R' F' F' F' R' B B R' R' R' F' R' B B R' R'
  := R'*F'*F'*F'*R'*B*B*R'*R'*R'*F'*R'*B*B*R'*R'
  -- #eval G4Perm
  -- ({ permute := ![0, 3, 1, 2, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
  def G4Perm_List:List RubiksSuperType := [R',F',F',F',R',B,B,R',R',R',F',R',B,B,R',R']

  /-- 是一个棱块3循环 ρ(g4) =(1,2,4) 这里指绝对位置1的块的新位置是绝对位置2；相当于逆时针 -/
  def G3Perm : RubiksSuperType -- R U' R U R U R U' R' U' R R
  := R*U'*R*U*R*U*R*U'*R'*U'*R*R
  -- #eval G3Perm
  --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  --  { permute := ![1, 3, 2, 0, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
  def G3Perm_List:List RubiksSuperType := [R,U',R,U,R,U,R,U',R',U',R,R]

  /-- 创建一阶交换子公式。不强制要求：r1影响到的块的集合A，与r2影响到的块的集合B，交集有且仅有1个（这就是为什么称作一阶）。 -/
  def conjugate_formula : RubiksSuperType → RubiksSuperType → RubiksSuperType
  := fun r1 r2 => r1 * r2 * r1⁻¹
  -- #eval conjugate_formula (D'*L*L) G4Perm  -- 比如：(2,3,6)交换子
  -- ({ permute := ![0, 5, 1, 3, 4, 2, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
  -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  abbrev conj := conjugate_formula

  end rubikCubeFormula

  -- 角块的排位：8个
  def UFL_index :Fin 8 := 0
  def UFR_index :Fin 8 := 1
  def UBR_index :Fin 8 := 2
  def UBL_index :Fin 8 := 3
  def DFL_index :Fin 8 := 4
  def DFR_index :Fin 8 := 5
  def DBR_index :Fin 8 := 6
  def DBL_index :Fin 8 := 7
  -- 棱块的排位：12个
  def UF_index :Fin 12 := 0
  def UR_index:Fin 12 := 1
  def UB_index :Fin 12 := 2
  def UL_index :Fin 12 := 3
  def FL_index :Fin 12 := 4
  def FR_index :Fin 12 := 5
  def RB_index :Fin 12 := 6
  def LB_index :Fin 12 := 7
  def FD_index :Fin 12 := 8
  def RD_index :Fin 12 := 9
  def BD_index :Fin 12 := 10
  def LD_index :Fin 12 := 11

    -- 魔方基本定理的左推右部分：done 主要用到代入验证和群的封闭性
  theorem reachable_valid
  : ∀x : RubiksSuperType, Reachable x → x ∈ ValidCube
  := by
    intro x hrx
    induction hrx with -- 这里induction其实是分类讨论：
    | Solved =>
        simp only [Solved, ValidCube]
        decide
    | FT c hc =>
      cases hc with
      | _ =>
        simp only [ValidCube]
        all_goals decide
    | mul a b hra hrb a_ih a_ih_1 =>
      -- 归纳证明：
      -- 对于某个项(x*y),假设Reachable (x*y),要推出（x*y） ∈ ValidCube
      -- 由于Reachable.mul的构造，Reachable (x*y)实际上还有2个前提的真命题：Reachable x , Reachable y
      -- 归纳证明提供了一个归纳假设：假设乘积项的长度小于(x*y)的都满足原命题；换句话说，对于x,y, 满足: x∈ ValidCube, y ∈ ValidCube
      -- 现在目标是：推出（x*y） ∈ ValidCube
      -- have Rxy: Reachable (a*b) := Reachable.mul a b hra hrb
      apply RubiksGroup.mul_mem' -- 反推一步，两个元素都是
      · exact a_ih
      · exact a_ih_1
    | inv c hc hc2 =>
      -- hc2可以理解成：任意长度都已经证明∈ ValidCube
      simp only [ValidCube]
      simp only [Set.mem_setOf_eq]
      simp only [Prod.fst_inv]
      simp only [PieceState.inv_def]
      simp only [Prod.snd_inv]
      simp only [PieceState.inv_def]
      apply And.intro
      {
        simp only [ps_inv]
        simp only [map_inv]
        have h1 := hc2.1
        rw [h1]
      }
      apply And.intro
      {
        simp only [ps_inv]
        simp only [Pi.neg_apply]
        simp only [Finset.sum_neg_distrib]
        simp only [neg_eq_zero]
        simp only [ValidCube] at hc2
        obtain ⟨hc3,hc4,hc5⟩:= hc2
        apply mul_mem'_permuteRemainsSum_2
        exact hc4
        done
      }
      { simp only [ps_inv]
        simp only [Pi.neg_apply]
        simp only [Finset.sum_neg_distrib]
        simp only [neg_eq_zero]
        simp only [ValidCube] at hc2
        obtain ⟨hc3,hc4,hc5⟩:= hc2
        apply mul_mem'_permuteRemainsSum
        exact hc5
        done
      }
    done




  section lemma1TrashCode
  --以下定理(lemma1_007_and008~001)用于lemma1证明的分类讨论，lemma2同理(lemma2_011_and012~001)
  --lemma1:存在操作h,当g满足角块方向和模3为0时，g*h还原所有角块方向至0，且不改变所有块位置及棱块方向
  --lemma2:存在操作h,当g满足棱块方向和模3为0时，g*h还原所有棱块方向至0，且不改变所有块位置及角块方向
    lemma lemma1_013:(F * G1Perm * F').2.orient = 0
    := by
      decide
      done

    lemma lemma1_012
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F^2 * G1Perm^2 * F^2)).1.orient = 0
    := by
      intro hsum
      have h2: Finset.sum {0, 1, 2,3,4,5,6,7} (F ^ 2 * G1Perm ^ 2 * F ^ 2).1.orient = 0 := by decide
      apply psmul0orientAction_orientRemainsSum g (F ^ 2 * G1Perm ^ 2 * F ^ 2) h2 hsum
      done

    lemma lemma1_011:(F^2 * G1Perm^2 * F^2).1.permute = 1
    := by
      decide
      done

    lemma lemma1_010
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F^2 * G1Perm * F^2)).1.orient = 0
    := by
      intro hsum
      have h2: Finset.sum {0, 1, 2,3,4,5,6,7} (F^2 * G1Perm * F^2).1.orient = 0 := by decide
      apply psmul0orientAction_orientRemainsSum g (F^2 * G1Perm * F^2) h2 hsum
      done

    lemma lemma1_009:(F^2 * G1Perm * F^2).1.permute = 1
    := by
      decide
      done

    lemma lemma1_008
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F * G1Perm^2 * F')).1.orient = 0
    := by
      intro hsum
      have h2: Finset.sum {0, 1, 2,3,4,5,6,7} (F * G1Perm^2 * F').1.orient = 0 := by decide
      apply psmul0orientAction_orientRemainsSum g (F * G1Perm^2 * F') h2 hsum
      done

    lemma lemma1_007:(F * G1Perm^2 * F').1.permute = 1
    := by
      decide
      done

    lemma lemma1_006:(F * G1Perm * F').1.permute = 1
    := by
      decide
      done

    lemma lemma1_005
    (g:RubiksSuperType)
    :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0
    →
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * (F * G1Perm * F')).1.orient = 0
    := by
      intro hsum
      have h2: Finset.sum {0, 1, 2,3,4,5,6,7} (F * G1Perm * F').1.orient = 0 := by decide
      apply psmul0orientAction_orientRemainsSum g (F * G1Perm * F') h2 hsum
      done


    -- 引理1最后一步，推出矛盾即可。
    lemma lemma1_007_UFR_and008DBL
    (g : RubiksSuperType)
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0 ∧ (Corner_Absolute_Orient g.1 UBR_index) = 0 ∧ (Corner_Absolute_Orient g.1 DBR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UFR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    (Corner_Absolute_Orient g.1 DBL_index) = 0
    ∧
    Reachable h
    := by
      let h := Solved
      have h_CAO_DBL_is0: Corner_Absolute_Orient g.1 DBL_index = 0
      := by
        -- 用h1 , h2即可
        simp only [Corner_Absolute_Orient] at h2 ⊢
        sorry
        -- done
      -- method 1:
      use 1
      apply And.intro
      {exact { left := rfl, right := { left := rfl, right := rfl } }}
      apply And.intro
      { simp only [mul_one]
        sorry
        -- done
      }
      apply And.intro
      {
        simp only [mul_one]
      }
      apply And.intro
      apply And.intro
      {
        simp only [mul_one]
      }
      {
        simp only [mul_one]
      }
      apply And.intro
      {
        exact h_CAO_DBL_is0
      }
      {
        simp only [Solved_eq_1, solved_reachable]
      }
      done


    lemma lemma1_006_DBR
    (g : RubiksSuperType)
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0 ∧ (Corner_Absolute_Orient g.1 UBR_index) = 0 ∧ (Corner_Absolute_Orient g.1 DBR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    Reachable h
    := by sorry

    lemma lemma1_005_UBR
    (g : RubiksSuperType)
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0 ∧ (Corner_Absolute_Orient g.1 UBR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    Reachable h
    := by sorry --

    lemma lemma1_004_UBL
    (g : RubiksSuperType)
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0
      ∧ (Corner_Absolute_Orient g.1 UBL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    Reachable h
    := by sorry --

    lemma lemma1_003_DFR
    (g : RubiksSuperType)
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFR_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    Reachable h
    := by sorry --

    lemma lemma1_002_DFL
    (g : RubiksSuperType)
    (h1: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (h2: (Corner_Absolute_Orient g.1 UFL_index) = 0 ∧ (Corner_Absolute_Orient g.1 DFL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    Reachable h
    := by sorry --

    -- lemma1的主要证明依赖本引理lemma1_001_UFL，本引理主要证明依赖lemma1_002_DFL
    -- 任意H中的状态，满足：角块方向数求和后模3为0,UFL的方向数为0
      -- 则=>存在G中操作h，(g*h)还原所有角块的方向数，且不改变全体棱块的方向数，且不改变所有块的位置。
    -- 思路：还原DFL的方向数后，使用lemma1_002_DFL即可。
    lemma lemma1_001_UFL
    (g : RubiksSuperType)
    (hsum0: Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0)
    (hCAO_UFL_0: (Corner_Absolute_Orient g.1 UFL_index) = 0)
    :
    ∃ h ∈ RubiksGroup ,
    (g * h).fst.orient = 0
    ∧
    (g).2.orient = (g * h).2.orient
    ∧
    ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
    ∧
    Reachable h
    := by
      let h := Solved
      by_cases ha0 : (Corner_Absolute_Orient g.1 DFL_index)=0
      {
        let moveAction1 := Solved
        have h1 := lemma1_002_DFL g hsum0 ({
          left := hCAO_UFL_0
          right := ha0
        })
        obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
        use h1_1
        done
      }
      { by_cases ha1: (Corner_Absolute_Orient g.1 DFL_index) = 1
        { let moveAction2 := F^2*G1Perm*F^2
          -- #eval F^2*G1Perm*F^2
          -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 2, 0, 0, 1] },
          --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
          -- 关键引理证明1:先找出从ha1发掘出的这个索引有什么用。
          have h2_1: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) (g.1.permute⁻¹ DFL_index)
          = g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction2.1.orient (DFL_index)
          := by
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
              Function.comp_apply, apply_inv_self]
            done
          simp only [Corner_Absolute_Orient] at ha1
          simp at ha1
          -- 关键引理证明2：先找出从ha1发掘出的这个索引有什么用。
          have h2_2: g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction2.1.orient (DFL_index) = 0
          := by
            simp only [Inv.inv]
            rw [ha1]
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
            have h2_2_1: (ps_mul (F ^ 2).1 (ps_mul G1Perm.1 (F ^ 2).1)).orient DFL_index = 2
            := by rfl
            rw [h2_2_1]
            rfl
            done
          have h2: (Corner_Absolute_Orient (g*moveAction2).1 DFL_index) = 0
          := by
            have _h2_1: (g.1.orient + moveAction2.1.orient ∘ ⇑g.1.permute) (g.1.permute⁻¹ DFL_index) = 0 := h2_1.trans h2_2
            simp only [Corner_Absolute_Orient]
            have _h2_3: (g * (F^2 * G1Perm * F^2)).1.permute = (g).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              rw [lemma1_009]
              rfl
            rw [_h2_3]
            have _h2_4: (g.1.orient + moveAction2.1.orient ∘ g.1.permute) = (g * (F^2 * G1Perm * F^2)).1.orient
              := by
              have _h2_4_1 := PieceState.mul_def g.1 (F^2 * G1Perm * F^2).1
              simp only [ps_mul] at _h2_4_1
              simp only [← Prod.fst_mul] at _h2_4_1
              rw [_h2_4_1]
              simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
              rw [add_comm]
              done
            rw [← _h2_4]
            exact _h2_1
            done
          simp only [Prod.fst_mul, Prod.snd_mul]
          have h2_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction2).1.orient = 0
            := by
            have h2_3_1 := lemma1_010 g hsum0
            simp only [moveAction2]
            exact h2_3_1
            done
          have h_b_2_4': Corner_Absolute_Orient (g * moveAction2).1 UFL_index = 0
            := by
            have h_MoveAction: (F^2*G1Perm*F^2).1.orient UFL_index  = 0
            := by decide
            have _h2_3: (g * moveAction2).1.permute = (g).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              have temp: (F ^ 2 * G1Perm * F ^ 2).1.permute = 1:=by decide
              rw [temp]
              rfl
            -- _h2_3 hCAO_UFL_0
            have temp := mulActon_CornerAbsoluteOrient_OneIndex_is0_2 0 0 0 rfl g moveAction2 UFL_index _h2_3 hCAO_UFL_0 h_MoveAction
            exact temp
            done
          have h2_4 := lemma1_002_DFL (g * moveAction2) h2_3 {
            left := h_b_2_4' -- Corner_Absolute_Orient (g * moveAction2).1 UFL_index = 0
            right := h2
          }
          obtain ⟨h2_4_1,h2_4_2,h2_4_3,h2_4_4,h2_4_5,h2_4_6⟩ := h2_4
          use (moveAction2 * h2_4_1)
          apply And.intro
          {simp only;
            -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
            sorry
            --done
          }
          apply And.intro
          { rw [← Prod.fst_mul]
            rw [← mul_assoc]
            exact h2_4_3
          }
          apply And.intro
          { rw [← Prod.snd_mul]
            rw [← mul_assoc]
            rw [← h2_4_4]
            have h2_4_4_1: g.2.orient = (g * moveAction2).2.orient
              := by
              rw [Prod.snd_mul]
              simp only [PieceState.mul_def]
              simp only [ps_mul]
              have temp: (F^2*G1Perm*F^2).2.orient =0 := by decide
              rw [temp]
              simp only [Pi.zero_comp, zero_add]
            exact h2_4_4_1
          }
          apply And.intro
          apply And.intro
          { rw [← Prod.fst_mul]
            rw [← mul_assoc]
            rw [← h2_4_5.1]
            have h2_4_5_1:g.1.permute = (g * moveAction2).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              have temp: (F^2*G1Perm*F^2).1.permute=1 := by decide
              rw [temp]
              rfl
            exact h2_4_5_1
          }
          { rw [← Prod.snd_mul]
            rw [← mul_assoc]
            rw [← h2_4_5.2]
            have h2_4_6_1: g.2.permute = (g * moveAction2).2.permute
              := by
              simp only [Prod.snd_mul]
              rw [permute_mul]
              rw [← Prod.snd_mul]
              rw [← Prod.snd_mul]
              have temp: (F^2*G1Perm*F^2).2.permute = 1 := by decide
              rw [temp]
              rfl
            exact h2_4_6_1
          }
          {
            apply Reachable.mul
            · sorry
            · exact h2_4_6
          }
        }
        { have ha2: Corner_Absolute_Orient g.1 DFL_index = 2
            := by
            sorry
          let moveAction3 := (F^2)*(G1Perm^2)*(F^2)
          have h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ DFL_index)
          = g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction3.1.orient (DFL_index)
          := by
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
              Function.comp_apply, apply_inv_self]
            done
          simp only [Corner_Absolute_Orient] at ha2
          simp at ha2
          -- 关键引理证明2
          have h3_2: g.1.orient (g.1.permute⁻¹ DFL_index) + moveAction3.1.orient (DFL_index) = 0
          := by
            simp only [Inv.inv]
            rw [ha2]
            simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
            have h3_2_1: (ps_mul (F ^ 2).1 (ps_mul (G1Perm ^ 2).1 (F ^ 2).1)).orient DFL_index = 1
            := by rfl
            -- rw [h3_2_1]
            rfl
            done
          have h3: (Corner_Absolute_Orient (g*moveAction3).1 DFL_index) = 0
          := by
            have _h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ DFL_index) = 0 := h3_1.trans h3_2
            simp only [Corner_Absolute_Orient]
            -- have _h3_2: (F^2 * G1Perm^2 * F^2).1.permute = 1
            -- 下面用lemma1_00?代替
            have _h3_3: (g * (F^2 * G1Perm^2  * F^2)).1.permute = (g).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              rw [lemma1_011]
              rfl
            rw [_h3_3]
            have _h3_4: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) = (g * (F^2 * G1Perm^2 * F^2)).1.orient
              := by
              have _h3_4_1 := PieceState.mul_def g.1 (F^2 * G1Perm^2 * F^2).1
              simp only [ps_mul] at _h3_4_1
              simp only [← Prod.fst_mul] at _h3_4_1
              rw [_h3_4_1]
              simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc]
              rw [add_comm]
              done
            rw [← _h3_4]
            exact _h3_1
            done
          simp only [Prod.fst_mul, Prod.snd_mul]
          have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction3).1.orient = 0
            := by
            have h3_3_1 := lemma1_012 g hsum0
            simp only [moveAction3]
            exact h3_3_1
            done
          have h_b_3:Corner_Absolute_Orient (g * moveAction3).1 UFL_index = 0
            := by
            have h_MoveAction: ((F^2)*(G1Perm^2)*(F^2)).1.orient UFL_index  = 0
            := by decide
            have _h2_3: (g * moveAction3).1.permute = (g).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              have temp: ((F^2)*(G1Perm^2)*(F^2)).1.permute = 1:=by decide
              rw [temp]
              rfl
            -- _h2_3 hCAO_UFL_0
            have temp := mulActon_CornerAbsoluteOrient_OneIndex_is0_2 0 0 0 rfl g moveAction3 UFL_index _h2_3 hCAO_UFL_0 h_MoveAction
            exact temp
            done
          have h3_4 := lemma1_002_DFL (g * moveAction3) h3_3 {
            left := h_b_3
            right := h3
          }
          obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
          use (moveAction3 * h3_4_1)
          apply And.intro
          {simp only;
            -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
            sorry
          }
          apply And.intro
          { rw [← Prod.fst_mul]
            rw [← mul_assoc]
            exact h3_4_3
          }
          apply And.intro
          { rw [← Prod.snd_mul]
            rw [← mul_assoc]
            rw [← h3_4_4]
            have h3_4_4_1: g.2.orient = (g * moveAction3).2.orient
              := by
              rw [Prod.snd_mul]
              simp only [PieceState.mul_def]
              simp only [ps_mul]
              have temp: ((F^2)*(G1Perm^2)*(F^2)).2.orient =0 := by decide
              rw [temp]
              simp only [Pi.zero_comp, zero_add]
            exact h3_4_4_1
          }
          apply And.intro
          apply And.intro
          { rw [← Prod.fst_mul]
            rw [← mul_assoc]
            rw [← h3_4_5.1]
            have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
              := by
              simp only [Prod.fst_mul]
              rw [permute_mul]
              rw [← Prod.fst_mul]
              rw [← Prod.fst_mul]
              have temp: ((F^2)*(G1Perm^2)*(F^2)).1.permute=1 := by decide
              rw [temp]
              rfl
            exact h3_4_5_1
          }
          { rw [← Prod.snd_mul]
            rw [← mul_assoc]
            rw [← h3_4_5.2]
            have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
              := by
              simp only [Prod.snd_mul]
              rw [permute_mul]
              rw [← Prod.snd_mul]
              rw [← Prod.snd_mul]
              have temp: ((F^2)*(G1Perm^2)*(F^2)).2.permute = 1 := by decide
              rw [temp]
              rfl
            exact h3_4_6_1
          }
          {
            apply Reachable.mul
            · sorry
            · exact h3_4_6
          }
        }
      }
      done

  -- 任意H中的状态，满足角块方向数求和后模3为0,
    -- 则=>存在G中操作h，(g*h)还原所有角块的方向数，且不改变全体棱块的方向数，且不改变所有块的位置。
  @[simp]
  lemma lemma1
  : ∀g : RubiksSuperType, -- RubiksSuperType即手写的H。
  Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) g.fst.orient = 0 --角块方向数求和后，模3为0。
  →
  ∃ h ∈ RubiksGroup ,
  (g * h).fst.orient = 0 -- 角块方向增加量归零
  ∧
  (g).2.orient = (g * h).2.orient -- 不变
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute) -- 不变
  ∧
  Reachable h
  := by
    intro g hsum0
    let h := Solved
    by_cases ha0 : (Corner_Absolute_Orient g.1 UFL_index)=0
    {
      let moveAction1 := Solved
      have h1 := lemma1_001_UFL g hsum0 ha0 -- 强力助手lemma1_001_UFL
      obtain ⟨solution0,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
      use solution0
      done
    }
    { by_cases ha1: (Corner_Absolute_Orient g.1 UFL_index) = 1
      { let moveAction2 := F*G1Perm*F'
        -- #eval F*G1Perm*F'
        -- ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![2, 0, 0, 0, 0, 0, 0, 1] },
        -- { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
        have h2: (Corner_Absolute_Orient (g*moveAction2).1 UFL_index) = 0
        := by
          have h_MoveAction: (F * G1Perm * F').1.orient UFL_index  = 2
            := by decide
          simp only [Corner_Absolute_Orient]
          have _h2_3: (g * (F * G1Perm * F')).1.permute = (g).1.permute
            := by
            simp only [Prod.fst_mul]
            rw [permute_mul]
            rw [← Prod.fst_mul]
            rw [← Prod.fst_mul]
            rw [lemma1_006]
            rfl
          apply mulActon_CornerAbsoluteOrient_OneIndex_is0
          · exact _h2_3
          · exact ha1
          · exact h_MoveAction
          done
        simp only [Prod.fst_mul]
        simp only [Prod.snd_mul]
        have h2_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction2).1.orient = 0
          := by
          have h2_3_1 := lemma1_005 g hsum0
          simp only [moveAction2]
          exact h2_3_1
          done
        have h2_4 := lemma1_001_UFL (g * moveAction2) h2_3 h2
        obtain ⟨moveAction3,h2_4_2,h2_4_3,h2_4_4,h2_4_5,h2_4_6⟩ := h2_4
        use (moveAction2 * moveAction3)
        apply And.intro
        { simp only
          -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
          have temp: Reachable (F * G1Perm * F' * moveAction3) := by sorry
          have temp2:(F * G1Perm * F' * moveAction3) ∈ ValidCube
            := by
            apply reachable_valid (F * G1Perm * F' * moveAction3) temp
          exact temp2
        }
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          exact h2_4_3
        }
        apply And.intro
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h2_4_4]
          have h2_4_4_1: g.2.orient = (g * moveAction2).2.orient
            := by
            rw [Prod.snd_mul]
            simp only [PieceState.mul_def]
            simp only [ps_mul]
            rw [lemma1_013]
            simp only [Pi.zero_comp, zero_add]
            done
          exact h2_4_4_1
        }
        apply And.intro
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          rw [← h2_4_5.1]
          have h2_4_5_1:g.1.permute = (g * moveAction2).1.permute
            := by
            simp only [Prod.fst_mul]
            rw [permute_mul]
            rw [← Prod.fst_mul]
            rw [← Prod.fst_mul]
            have temp: (F * G1Perm * F').1.permute =1 := by decide
            rw [temp]
            rfl
          exact h2_4_5_1
        }
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h2_4_5.2]
          have h2_4_6_1: g.2.permute = (g * moveAction2).2.permute
            := by
            simp only [Prod.snd_mul]
            rw [permute_mul]
            rw [← Prod.snd_mul]
            rw [← Prod.snd_mul]
            have temp: (F * G1Perm * F').2.permute = 1 := by decide
            rw [temp]
            rfl
          exact h2_4_6_1
        }
        {
          apply Reachable.mul
          · sorry
          · exact h2_4_6
        }
      }
      -- 最后一个分类:
      { have ha2: Corner_Absolute_Orient g.1 UFL_index = 2
          := by
          sorry
        let moveAction3 := F*(G1Perm^2)*F'
        have h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ UFL_index)
        = g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction3.1.orient (UFL_index)
        := by
          simp only [Prod.fst_mul]
          simp only [PieceState.mul_def]
          simp only [ps_mul_assoc]
          simp only [Pi.add_apply]
          simp only [Function.comp_apply]
          simp [Corner_Absolute_Orient] at ha1
          have temp: g.1.permute⁻¹ = g.1.permute.symm := by exact rfl
          rw [temp]
          simp only [apply_symm_apply]
          done
        simp only [Corner_Absolute_Orient] at ha2
        simp at ha2
        -- 关键引理证明2
        have h3_2: g.1.orient (g.1.permute⁻¹ UFL_index) + moveAction3.1.orient (UFL_index) = 0
        := by
          simp only [Inv.inv]
          rw [ha2]
          simp only [Prod.fst_mul]
          simp only [PieceState.mul_def]
          simp only [ps_mul_assoc]
          have h3_2_1: (ps_mul F.1 (ps_mul (G1Perm ^ 2).1 F'.1)).orient UFL_index = 1
          := by rfl
          rw [h3_2_1]
          rfl
          done
        have h3: (Corner_Absolute_Orient (g*moveAction3).1 UFL_index) = 0
        := by
          have _h3_1: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) (g.1.permute⁻¹ UFL_index) = 0 := h3_1.trans h3_2
          simp only [Corner_Absolute_Orient]
          -- have _h3_2: (F * G1Perm^2 * F').1.permute = 1
          -- 下面用lemma1_007代替
          -- simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, invFun_as_coe]
          have _h3_3: (g * (F * G1Perm^2  * F')).1.permute = (g).1.permute
            := by
            simp only [Prod.fst_mul]
            rw [permute_mul]
            rw [← Prod.fst_mul]
            rw [← Prod.fst_mul]
            rw [lemma1_007]
            rfl
          rw [_h3_3]
          have _h3_4: (g.1.orient + moveAction3.1.orient ∘ g.1.permute) = (g * (F * G1Perm^2 * F')).1.orient
            := by
            have _h3_4_1 := PieceState.mul_def g.1 (F * G1Perm^2 * F').1
            simp only [ps_mul] at _h3_4_1
            simp only [← Prod.fst_mul] at _h3_4_1
            rw [_h3_4_1]
            simp only [Prod.fst_mul]
            simp only [PieceState.mul_def]
            simp only [ps_mul_assoc]
            rw [add_comm]
            done
          rw [← _h3_4]
          exact _h3_1
          done
        simp only [Prod.fst_mul, Prod.snd_mul]
        have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * moveAction3).1.orient = 0
          := by
          have h3_3_1 := lemma1_008 g hsum0
          simp only [moveAction3]
          exact h3_3_1
          done
        have h3_4 := lemma1_001_UFL (g * moveAction3) h3_3 h3
        obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
        use (moveAction3 * h3_4_1)
        apply And.intro
        { simp only
          -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
          have temp: Reachable (F * G1Perm ^ 2 * F' * h3_4_1) := by sorry
          have temp2:(F * G1Perm ^ 2 * F' * h3_4_1) ∈ ValidCube
            := by
            apply reachable_valid (F * G1Perm ^ 2 * F' * h3_4_1) temp
          exact temp2
        }
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          exact h3_4_3
        }
        apply And.intro
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h3_4_4]
          have h3_4_4_1: g.2.orient = (g * moveAction3).2.orient
            := by
            rw [Prod.snd_mul]
            simp only [PieceState.mul_def]
            simp only [ps_mul]
            have temp: (F*(G1Perm^2)*F').2.orient =0 := by decide
            rw [temp]
            simp only [Pi.zero_comp, zero_add]
          exact h3_4_4_1
        }
        apply And.intro
        apply And.intro
        { rw [← Prod.fst_mul]
          rw [← mul_assoc]
          rw [← h3_4_5.1]
          have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
            := by
            simp only [Prod.fst_mul]
            rw [permute_mul]
            rw [← Prod.fst_mul]
            rw [← Prod.fst_mul]
            have temp: (F * G1Perm ^ 2 * F').1.permute=1 := by decide
            rw [temp]
            rfl
          exact h3_4_5_1
        }
        { rw [← Prod.snd_mul]
          rw [← mul_assoc]
          rw [← h3_4_5.2]
          have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
            := by
            simp only [Prod.snd_mul]
            rw [permute_mul]
            rw [← Prod.snd_mul]
            rw [← Prod.snd_mul]
            have temp: (F*(G1Perm^2)*F').2.permute = 1 := by decide
            rw [temp]
            rfl
          exact h3_4_6_1
        }
        {
          apply Reachable.mul
          · sorry
          · exact h3_4_6
        }
      }
    }
    done

      --给出详细的步骤h，使得(g * h).1.orient = 0成立：
      -- 1.首先还原F面的3个角块:UFL,DFL,DFR：
        -- 1.还原UFL的方向数：分类讨论：
          -- 1.UFL的方向数为0,h=h
          -- 2.UFL的方向数为1,h=h*F*G1*F'
          -- 3.UFL的方向数为2,h=h*F*(G1^2)*F'
        -- 2.还原DFL的方向数：分类讨论：
          -- 1.DFL的方向数为0,h=h
          -- 2.DFL的方向数为1,h=h*F^2*G1*F^2
          -- 3.DFL的方向数为2,h=h*F^2*(G1^2)*F^2
        -- ...

  end lemma1TrashCode


  section lemma2TrashCode

  lemma lemma2_006
  (g:RubiksSuperType)
  :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} g.2.orient = 0
  →
  Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g * (R * G2Perm * R')).2.orient = 0
  := by
    intro hsum
    have h2: Finset.sum {0, 1, 2,3,4,5,6,7} (R * G2Perm * R').2.orient = 0 := by decide
    apply psmul0orientAction_orientRemainsSum_2 g (R * G2Perm * R') h2 hsum
    done

  lemma lemma2_005:(R * G2Perm * R').2.permute = 1
  := by
    decide
    done

  lemma lemma2_004
  (g:RubiksSuperType)
  :Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} g.2.orient = 0
  →
  Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g*G2Perm).2.orient = 0
  := by
    intro hsum
    have h2: Finset.sum {0, 1, 2,3,4,5,6,7} G2Perm.2.orient = 0 := by decide
    apply psmul0orientAction_orientRemainsSum_2 g G2Perm h2 hsum
    done

  lemma lemma2_003:(G2Perm).2.permute = 1 := by decide

  lemma lemma2_011_UL_and_012_UF
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FL_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UL_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  (Edge_Absolute_Orient g.2 UF_index) = 0
  ∧
  Reachable h
  := by
    let h := Solved
    have h_EAO_UF_is0: Edge_Absolute_Orient g.2 UF_index = 0
    := by
      simp only [Edge_Absolute_Orient] at h2 ⊢
      sorry
      -- done
    use 1
    apply And.intro
    {
      simp only [← Solved_eq_1]
      apply reachable_valid
      simp only [Solved_eq_1, solved_reachable]
    }
    apply And.intro
    {
      -- h2 , h_EAO_UF_is0
      sorry
      --done
    }
    apply And.intro
    {
      simp only [mul_one]
    }
    apply And.intro
    apply And.intro
    {
      simp only [mul_one]
    }
    {
      simp only [mul_one]
    }
    apply And.intro
    {exact h_EAO_UF_is0}
    {simp only [Solved_eq_1, solved_reachable]}
    done



  lemma lemma2_010_FD
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FL_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FD_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry --

  lemma lemma2_009_FL
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0
  ∧ (Edge_Absolute_Orient g.2 FL_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry --

  lemma lemma2_008_LD
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 LD_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry --

  lemma lemma2_007_LB
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0 ∧ (Edge_Absolute_Orient g.2 LB_index) = 0)
  :
  ∃ h ∈ RubiksGroup,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry --

  lemma lemma2_006_BD
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0 ∧ (Edge_Absolute_Orient g.2 BD_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry --

  lemma lemma2_005_UB
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0
  ∧ (Edge_Absolute_Orient g.2 UB_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry--

  lemma lemma2_004_RB
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0 ∧ (Edge_Absolute_Orient g.2 RB_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry--

  lemma lemma2_003_RD
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0 ∧ (Edge_Absolute_Orient g.2 RD_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry--

  lemma lemma2_002_FR
  (g : RubiksSuperType)
  (h1: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.2.orient = 0)
  (h2: (Edge_Absolute_Orient g.2 UR_index) = 0 ∧ (Edge_Absolute_Orient g.2 FR_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by sorry --

  -- 任意H中的状态，满足：棱块方向数求和后模2为0,UR的方向数为0
    -- 则=>存在G中操作h，(g*h)还原所有棱块的方向数，且不改变全体角块的方向数，且不改变所有块的位置。
  -- 思路：还原FR
  lemma lemma2_001_UR
  (g : RubiksSuperType)
  (hsum0: Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.snd.orient = 0)
  (h_EAO_UR_0: (Edge_Absolute_Orient g.2 UR_index) = 0)
  :
  ∃ h ∈ RubiksGroup ,
  (g * h).2.orient = 0
  ∧
  (g).1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by
    let h := Solved
    by_cases ha0 : (Edge_Absolute_Orient g.2 FR_index)=0
    {
      let moveAction1 := Solved
      have h1 := lemma2_002_FR g hsum0 ({
        left := h_EAO_UR_0
        right := ha0
      })
      obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
      use h1_1
      done
    }
    { have ha2: (Edge_Absolute_Orient g.2 FR_index) = 1
        := by
        sorry
      let moveAction3 := (R)*(G2Perm)*(R')
      have h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ FR_index)
      = g.2.orient (g.2.permute⁻¹ FR_index) + moveAction3.2.orient (FR_index)
      := by
        simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
          Function.comp_apply, apply_inv_self]
        done
      simp only [Edge_Absolute_Orient] at ha2
      simp at ha2
      have h3_2: g.2.orient (g.2.permute⁻¹ FR_index) + moveAction3.2.orient (FR_index) = 0
      := by
        simp only [Inv.inv]
        rw [ha2]
        simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
        have h3_2_1: (ps_mul R.2 (ps_mul G2Perm.2 R'.2)).orient FR_index = 1
        := by rfl
        -- rw [h3_2_1]
        rfl
        done
      have h3: (Edge_Absolute_Orient (g*moveAction3).2 FR_index) = 0
      := by
        have _h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ FR_index) = 0 := h3_1.trans h3_2
        simp only [Edge_Absolute_Orient]
        -- have _h3_2: (F^2 * G1Perm^2 * F^2).2.permute = 1
        -- 下面用lemma1_00?代替
        have _h3_3: (g * (R * G2Perm * R')).2.permute = (g).2.permute
          := by
          simp only [Prod.snd_mul]
          rw [permute_mul]
          rw [← Prod.snd_mul]
          rw [← Prod.snd_mul]
          rw [lemma2_005]
          rfl
        rw [_h3_3]
        have _h3_4: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) = (g * (R * G2Perm * R')).2.orient
          := by
          have _h3_4_1 := PieceState.mul_def g.2 (R * G2Perm * R').2
          simp only [ps_mul] at _h3_4_1
          simp only [← Prod.snd_mul] at _h3_4_1
          rw [_h3_4_1]
          simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
          rw [add_comm]
          done
        rw [← _h3_4]
        exact _h3_1
        done
      simp only [Prod.fst_mul, Prod.snd_mul]
      have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} (g * moveAction3).2.orient = 0
        := by
        have h3_3_1 := lemma2_006 g hsum0
        simp only [moveAction3]
        exact h3_3_1
        done
      have h_b_3:Edge_Absolute_Orient (g * moveAction3).2 UR_index = 0
        := by
        have h_MoveAction: ((R)*(G2Perm)*(R')).2.orient UR_index  = 0
        := by decide
        have _h2_3: (g * moveAction3).2.permute = (g).2.permute
          := by
          simp only [Prod.snd_mul]
          rw [permute_mul]
          rw [← Prod.snd_mul]
          rw [← Prod.snd_mul]
          have temp: ((R)*(G2Perm)*(R')).2.permute = 1:=by decide
          rw [temp]
          rfl
        have temp := mulActon_EdgeAbsoluteOrient_OneIndex_is0_2 0 0 0 rfl g moveAction3 UR_index _h2_3 h_EAO_UR_0 h_MoveAction
        exact temp
      have h3_4 := lemma2_002_FR (g * moveAction3) h3_3 {
        left := h_b_3
        right := h3
      }
      obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
      use (moveAction3 * h3_4_1)
      apply And.intro
      {simp only;
        -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
        sorry
        --done
      }
      apply And.intro
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        exact h3_4_3
      }
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_4]
        have h3_4_4_1: g.1.orient = (g * moveAction3).1.orient
          := by
          rw [Prod.fst_mul]
          simp only [PieceState.mul_def]
          simp only [ps_mul]
          have temp: ((R)*(G2Perm)*(R')).1.orient =0 := by decide
          rw [temp]
          simp only [Pi.zero_comp, zero_add]
        exact h3_4_4_1
      }
      apply And.intro
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_5.1]
        have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
          := by
          simp only [Prod.fst_mul]
          rw [permute_mul]
          rw [← Prod.fst_mul]
          rw [← Prod.fst_mul]
          have temp: ((R)*(G2Perm)*(R')).1.permute=1 := by decide
          rw [temp]
          rfl
        exact h3_4_5_1
      }
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        rw [← h3_4_5.2]
        have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
          := by
          simp only [Prod.snd_mul]
          rw [permute_mul]
          rw [← Prod.snd_mul]
          rw [← Prod.snd_mul]
          have temp: ((R)*(G2Perm)*(R')).2.permute = 1 := by decide
          rw [temp]
          rfl
        exact h3_4_6_1
      }
      {
        apply Reachable.mul
        · sorry
        · exact h3_4_6
      }
    }
    done



  -- 还原所有棱块的方向数,且不改变全体角块的方向数，且不改变所有块的位置。
  lemma lemma2
  : ∀g : RubiksSuperType,
  Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) g.snd.orient = 0

  →

  ∃ h ∈ RubiksGroup ,
  (g * h).snd.orient = 0
  ∧
  g.1.orient = (g * h).1.orient
  ∧
  ((g).1.permute = (g * h).1.permute ∧ (g).2.permute = (g * h).2.permute)
  ∧
  Reachable h
  := by
    intro g hsum0
    let h:= Solved
    by_cases ha0 : (Edge_Absolute_Orient g.2 UR_index)=0
    {
      let moveAction1 := Solved
      have h1 := lemma2_001_UR g hsum0 ha0
      obtain ⟨h1_1,h1_2,h1_3,h1_4,h1_5,h1_6⟩ := h1
      use h1_1
      done
    }
    { have ha2: (Edge_Absolute_Orient g.2 UR_index)=1
        := by
        sorry
      let moveAction3 := (G2Perm)
      -- #eval G2Perm
      --   ({ permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
      --  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })
      have h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ UR_index)
      = g.2.orient (g.2.permute⁻¹ UR_index) + moveAction3.2.orient (UR_index)
      := by
        simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Pi.add_apply,
          Function.comp_apply, apply_inv_self]
        done
      simp only [Edge_Absolute_Orient] at ha2
      simp at ha2
      have h3_2: g.2.orient (g.2.permute⁻¹ UR_index) + moveAction3.2.orient (UR_index) = 0
      := by
        simp only [Inv.inv]
        rw [ha2]
        -- simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
        have h3_2_1: G2Perm.2.orient UR_index = 1
        := by rfl
        rw [h3_2_1]
        rfl
        done
      have h3: (Edge_Absolute_Orient (g*moveAction3).2 UR_index) = 0
        := by
          have _h3_1: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) (g.2.permute⁻¹ UR_index) = 0 := h3_1.trans h3_2
          simp only [Edge_Absolute_Orient]
          -- have _h3_2: (G2Perm).2.permute = 1
          -- 下面用lemma1_007代替
          -- simp only [Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, invFun_as_coe]
          have _h3_3: (g * (G2Perm)).2.permute = (g).2.permute
            := by
            simp only [Prod.snd_mul]
            rw [permute_mul]
            rw [lemma2_003]
            rfl
          rw [_h3_3]
          have _h3_4: (g.2.orient + moveAction3.2.orient ∘ g.2.permute) = (g * (G2Perm)).2.orient
            := by
            have _h3_4_1 := PieceState.mul_def g.2 (G2Perm).2
            simp only [ps_mul] at _h3_4_1
            simp only [← Prod.snd_mul] at _h3_4_1
            rw [_h3_4_1]
            simp only [Prod.snd_mul, PieceState.mul_def, ps_mul_assoc]
            rw [add_comm]
            done
          rw [← _h3_4]
          exact _h3_1
          done
      simp only [Prod.fst_mul, Prod.snd_mul]
      have h3_3 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g * moveAction3).2.orient = 0
        := by
        have h3_3_1 := lemma2_004 g hsum0
        simp only [moveAction3]
        exact h3_3_1
        done
      have h3_4 := lemma2_001_UR (g * moveAction3) h3_3 h3
      obtain ⟨h3_4_1,h3_4_2,h3_4_3,h3_4_4,h3_4_5,h3_4_6⟩ := h3_4
      use (moveAction3 * h3_4_1)
      apply And.intro
      {simp only;
        -- 这个就是因为是reachable，也是validcube，所以也是属于rubiksgroup
        sorry
        --done
      }
      apply And.intro
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        exact h3_4_3
      }
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_4]
        have h3_4_4_1: g.1.orient = (g * moveAction3).1.orient
          := by
          rw [Prod.fst_mul]
          simp only [PieceState.mul_def]
          simp only [ps_mul]
          have temp: (G2Perm).1.orient =0 := by decide
          rw [temp]
          simp only [Pi.zero_comp, zero_add]
        exact h3_4_4_1
      }
      apply And.intro
      apply And.intro
      { rw [← Prod.fst_mul]
        rw [← mul_assoc]
        rw [← h3_4_5.1]
        have h3_4_5_1:g.1.permute = (g * moveAction3).1.permute
          := by
          simp only [Prod.fst_mul]
          rw [permute_mul]
          have temp: (G2Perm).1.permute=1 := by decide
          rw [temp]
          rfl
        exact h3_4_5_1
      }
      { rw [← Prod.snd_mul]
        rw [← mul_assoc]
        rw [← h3_4_5.2]
        have h3_4_6_1: g.2.permute = (g * moveAction3).2.permute
          := by
          simp only [Prod.snd_mul]
          rw [permute_mul]
          have temp: (G2Perm).2.permute = 1 := by decide
          rw [temp]
          rfl
        exact h3_4_6_1
      }
      {
        apply Reachable.mul
        · sorry
        · exact h3_4_6
      }
    }
    done

  end lemma2TrashCode



  def remains_allOrient_and_edgePermute --只有角块是乱的
  (x : RubiksSuperType)  : Prop
  := x.1.orient=0 ∧ x.2.orient=0 ∧ x.2.permute=1
  def remains_allOrient_and_cornerPermute --只有棱块是乱的
  (x : RubiksSuperType)  : Prop
  := x.1.orient=0 ∧ x.2.orient=0 ∧ x.1.permute=1

  -- 角块部分：
  def exist_reachableG_cornerPermute_to1 --能还原角块位置
  (x : RubiksSuperType)  : Prop
  :=
    ∃ g : RubiksSuperType,
      Reachable g
      ∧
      (x * g).1.permute = 1
      ∧
      (x * g).1.orient = (x).1.orient
      ∧
      (x * g).2.orient = (x).2.orient
      ∧
      (x * g).2.permute = (x).2.permute

  def permFin8_to_RubiksSuperType --由8-置换得到对应的超群
  : (Perm (Fin 8)) → RubiksSuperType
  := by
    exact fun x => {
      fst := {
        permute := x
        orient := 0
      }
      snd := {
        permute := 1
        orient := 0
      }
    }

  -- def xx1: RubiksSuperType := sorry
  -- #check xx1 * (F*R)

 --存在3循环置换只改变3个角块的位置使其复原，其余不改变
  lemma alternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
  (g: RubiksSuperType)
  (threeList: List (Perm (Fin 8)) )
  (h1: ∀a ∈ threeList, IsThreeCycle a)
  (h2: g.1.permute = threeList.prod)
  :∃ (rubiksList:List RubiksSuperType) (rst1:RubiksSuperType),
  g =rst1 * rubiksList.prod
  ∧
  rst1.1.permute = 1
  ∧
  (g.1.orient=rst1.1.orient ∧ g.2.permute=rst1.2.permute ∧ g.2.orient=rst1.2.orient)
  ∧
  rubiksList = (threeList.map permFin8_to_RubiksSuperType) -- 映射得来
  := by
    let result_List: List RubiksSuperType := threeList.map permFin8_to_RubiksSuperType
    let result_rst1: RubiksSuperType := {
      fst := {
        permute := 1
        orient := g.1.orient
      }
      snd := {
        permute := g.2.permute
        orient := g.2.orient
      }
    }
    use result_List,result_rst1
    apply And.intro
    · simp only
      ext
      {
        have prod_map_change: List.prod (List.map permFin8_to_RubiksSuperType threeList)
        = permFin8_to_RubiksSuperType (List.prod threeList)
          := by
          simp only [permFin8_to_RubiksSuperType]
          sorry
        rw [prod_map_change]
        simp only [permFin8_to_RubiksSuperType]
        simp only [Prod.fst_mul, PieceState.mul_def]
        simp only [ps_mul]
        simp only [mul_one, Perm.coe_one, Function.comp_id, zero_add]
        rw [← h2]
      }
      {
        have prod_map_change: List.prod (List.map permFin8_to_RubiksSuperType threeList)
        = permFin8_to_RubiksSuperType (List.prod threeList)
          := by
          simp only [permFin8_to_RubiksSuperType]
          sorry
        rw [prod_map_change]
        simp only [permFin8_to_RubiksSuperType]
        rw [← h2]
        simp only [Prod.mk_mul_mk, PieceState.mul_def, ps_mul_one]
      }
    apply And.intro
    · exact rfl
    apply And.intro
    · exact { left := rfl, right := { left := rfl, right := rfl } }
    · exact rfl

  -- 棱块部分：
  def exist_reachableG_edgePermute_to1
  (x : RubiksSuperType)  : Prop
  :=
    ∃ g : RubiksSuperType,
      Reachable g
      ∧
      (x * g).2.permute = 1
      ∧
      (x * g).1.orient = (x).1.orient
      ∧
      (x * g).2.orient = (x).2.orient
      ∧
      (x * g).1.permute = (x).1.permute

  def permFin12_to_RubiksSuperType
  : (Perm (Fin 12)) → RubiksSuperType
  := by
    exact fun x => {
      fst := {
        permute := 1
        orient := 0
      }
      snd := {
        permute := x
        orient := 0
      }
    }
  --存在3循环置换只改变3个棱块的位置使其复原，其余不改变
  lemma alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
  (g: RubiksSuperType)
  (threeList: List (Perm (Fin 12)) )
  (h1: ∀a ∈ threeList, IsThreeCycle a)
  (h2: g.2.permute = threeList.prod)
  :∃ (rubiksList:List RubiksSuperType) (rst1:RubiksSuperType),
  g = rst1 * rubiksList.prod
  ∧
  rst1.2.permute = 1
  ∧
  -- 原始的3个项相等
  (g.1.orient=rst1.1.orient ∧ g.1.permute=rst1.1.permute ∧ g.2.orient=rst1.2.orient)
  ∧
  rubiksList = (threeList.map permFin12_to_RubiksSuperType) -- 映射得来
  := by
    let result_List: List RubiksSuperType := threeList.map permFin12_to_RubiksSuperType
    let result_rst1: RubiksSuperType := {
      fst := {
        permute := g.1.permute
        orient := g.1.orient
      }
      snd := {
        permute := 1
        orient := g.2.orient
      }
    }
    use result_List,result_rst1
    apply And.intro
    · simp only
      ext
      {
        simp only [Prod.fst_mul, PieceState.mul_def]
        sorry
      }
      {
        simp only [Prod.snd_mul, PieceState.mul_def]
        sorry
      }
    apply And.intro
    · exact rfl
    apply And.intro
    · exact { left := rfl, right := { left := rfl, right := rfl } }
    · exact rfl

  --辅助证明lemma31
  lemma lemma31_001 : Solved = ({ permute := List.formPerm ([1,2,3]:(List (Fin 8))), orient := 0 }, { permute := 1, orient := 0 }) * (G4Perm)
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [G4Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide
  lemma lemma31_002 : Solved =  ({ permute := List.formPerm ([1,0,6]:(List (Fin 8))) , orient := 0 }, { permute := 1, orient := 0 }) *
    (B * B * VariantFaceTurn_B_List [R', F', F', F', R', B, B, R', R', R', F', R', B, B, R', R'] * B * B)⁻¹
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, mul_inv_rev]
    simp only [VariantFaceTurn_B_List,VariantFaceTurn_B]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul]
    decide
  lemma lemma31_003' : Solved =  ({ permute := List.formPerm ([1,3,5]:(List (Fin 8))), orient := 0 }, { permute := 1, orient := 0 }) *
    (G4Perm*(conjugate_formula (D'*L*L) G4Perm)⁻¹)⁻¹
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [conjugate_formula,G4Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide

  -- #eval (G4Perm*(conjugate_formula (D'*L*L) G4Perm)⁻¹)⁻¹ = (conj (U*L2*U*L2*U') (conjugate_formula (D'*L*L) G4Perm)⁻¹)⁻¹


  lemma lemma31_003 : Solved =  ({ permute := List.formPerm ([1,3,5]:(List (Fin 8))), orient := 0 }, { permute := 1, orient := 0 }) *
    -- (conj (U*L2*U*L2*U') (conjugate_formula (D'*L*L) G4Perm)⁻¹)⁻¹
    (conj (D2*B2*D2*L2) G4Perm)⁻¹
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [conjugate_formula,G4Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide

    -- conj (U*L2*U*L2*U') (conjugate_formula (D'*L*L) G4Perm)⁻¹



  /-- 如果状态x的角块的位置是一个三循环（全体方向数已还原,棱块位置已还原），则存在G中复合操作g，使得（x*g）的位置是复原状态。 -/
  lemma lemma31 -- 这个命题直接上就是给出其中算法将角块3循环（全体方向数已还原,棱块位置已还原）还原到1。
  -- 用到公式有3类：1.g4 ; 2.g4的4种列表映射得到的变式(VariantFaceTurn_?_List) ； 3.包含g4（或g4变式）的交换子（conjugate_formula）。
  (x : RubiksSuperType)
  (h1: IsThreeCycle x.1.permute)
  (h2: x.1.orient =0)
  (h3: x.2.permute = 1)
  (h4: x.1.orient =0)
  : Reachable x
  := by
    -- 开展分类56种讨论。先看IsThreeCycle为条件的一些定理证明
    -- G4Perm效果：ρ(g4) =(2,4,3) ： 顺时针
    -- 人为的等价分类：1.“变式的”，即“同形状”的是等价的。
    -- 需要一个制造排列 Perm (Fin 8)的函数。应该是从List (Fin 8) → Perm (Fin 8)。
    have x_eq_Solvedx : x = Solved * x := by exact self_eq_mul_left.mpr rfl
    -- 先进行一个小分类的推理：原2在3，原3在4，原4在2。
    let p1 := List.formPerm ([1,2,3]:(List (Fin 8))) -- ![0, 2, 3, 1, 4, 5, 6, 7]
    -- 先进行一个小分类的推理：原3新在2，原2新在8，原8新在3。
    let p2 := List.formPerm ([1,0,6]:(List (Fin 8))) -- (2,1,7) == 这里的[1,0,6] -- ![0, 7, 1, 3, 4, 5, 6, 2]
    let p3 := List.formPerm ([1,3,5]:(List (Fin 8))) -- (2,4,6) == 这里的[1,3,5]
    by_cases ha0:x.1.permute = p1
      -- 执行一次G4Perm即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p1:RubiksSuperType := {
        fst := {
          permute := p1
          orient := 0
        }
        snd := {
          permute := 1
          orient := 0
        }
      }
      -- 由于 Solved * rubiks_p1 = x
      have x_eq_rubiks_p1: x = rubiks_p1
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        sorry
      have G4Perm_eq_rubiks_p1: rubiks_p1*G4Perm = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma31_001]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p1]
        have R_rubiks_p1_mul_G4Perm: Reachable (rubiks_p1 * G4Perm) := by
          rw [G4Perm_eq_rubiks_p1];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p1) (G4Perm) R_rubiks_p1_mul_G4Perm
        apply testaaa1
        sorry
    }
    by_cases ha0:x.1.permute = p2
      -- 执行：交换子(B*B*(VariantFaceTurn_B_List [R',F',F',F',R',B,B,R',R',R',F',R',B,B,R',R'])*B*B)⁻¹
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p2:RubiksSuperType := {
        fst := {
          permute := p2
          orient := 0
        }
        snd := {
          permute := 1
          orient := 0
        }
      }
      -- 由于 Solved * rubiks_p2 = x
      have x_eq_rubiks_p2: x = rubiks_p2
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        sorry
      let solution := (B*B*(VariantFaceTurn_B_List G4Perm_List)*B*B)⁻¹
      -- (2,4,3)
      -- (1,4,2)
      -- (1,7,2)
      have Solution_mul_rubiksp2_isOne: rubiks_p2 * solution = 1
        := by
        simp only [G4Perm_List]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma31_002]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p2]
        have R_rubiksp2_mul_Solution: Reachable (rubiks_p2 * solution) := by
          rw [Solution_mul_rubiksp2_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p2) (solution) R_rubiksp2_mul_Solution
        apply testaaa1
        sorry
    }
    by_cases ha0:x.1.permute = p3
    {
      let rubiks_p3:RubiksSuperType := {
        fst := {
          permute := p3
          orient := 0
        }
        snd := {
          permute := 1
          orient := 0
        }
      }
      -- x 和 rubiks_p3 是一回事：
      have x_eq_rubiks_p3: x = rubiks_p3
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        sorry
      let solution := (conj (D2*B2*D2*L2) G4Perm)⁻¹
      -- method1: (G4Perm*(conjugate_formula (D'*L*L) G4Perm )⁻¹)⁻¹
      -- method2: (conj (U*L2*U*L2*U') (conjugate_formula (D'*L*L) G4Perm)⁻¹)⁻¹
      -- method3: (conj (D2*B2*D2*L2) G4Perm)⁻¹
      -- (2,4,3)
      -- (2,4,6)
      have Solution_mul_rubiksp3_isOne: rubiks_p3 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma31_003]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p3]
        have R_rubiksp3_mul_Solution: Reachable (rubiks_p3 * solution) := by
          rw [Solution_mul_rubiksp3_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p3) (solution) R_rubiksp3_mul_Solution
        apply testaaa1
        sorry
    }
    sorry


  lemma lemma32_001 : Solved = ({ permute := 1, orient := 0 }, { permute := List.formPerm ([0,3,1]:(List (Fin 12))) , orient := 0 })  * (G3Perm)
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [G3Perm]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide
  lemma lemma32_002 : Solved =  ({ permute := 1, orient := 0 }, { permute := List.formPerm ([0,1,5]:(List (Fin 12))), orient := 0 }) *
    (conjugate_formula (U*L2*U'*L2) (conjugate_formula (F') G3Perm))
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one, mul_inv_rev]
    simp only [G3Perm,conjugate_formula]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul]
    decide
  lemma lemma32_003 : Solved =   ({ permute := 1, orient := 0 }, { permute := List.formPerm ([0,6,11]:(List (Fin 12))), orient := 0 }) *
    (conjugate_formula (U2*L2*U2) (conjugate_formula B (VariantFaceTurn_R_List G3Perm_List)))
    := by
    simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
    simp only [G3Perm,conjugate_formula]
    simp only [Solved_iff, Prod.fst_mul, PieceState.mul_def, ps_mul_assoc, Prod.snd_mul, ps_one_mul] -- ***这一行很重要，使得decide成为了可能。
    decide


  /-- 如果状态x的棱块的位置是一个三循环（全体方向数已还原,棱块位置已还原），则存在G中复合操作g，使得（x*g）的位置是复原状态。 -/
  lemma lemma32
  (x : RubiksSuperType)
  (h1: IsThreeCycle x.2.permute)
  (h2: x.2.orient =0)
  (h3: x.1.permute = 1)
  (h4: x.1.orient =0)
  : Reachable x
  := by
    -- 分类220种情况
    -- G3Perm效果： σ(g3) =(1,2,4): 逆时针
    have x_eq_Solvedx : x = Solved * x := by exact self_eq_mul_left.mpr rfl
    let p1 := List.formPerm ([0,3,1]:(List (Fin 12))) -- (1,4,2) == 这里的[0,3,1]  {0=>3,3=>1,1=>0}
    let p2 := List.formPerm ([0,1,5]:(List (Fin 12))) -- {1,2,6} == 这里的[0,1,5]
    let p3 := List.formPerm ([0,6,11]:(List (Fin 12))) -- {1,7,12} == 这里的[0,6,11]
    by_cases ha0:x.2.permute = p1
      -- 执行：G3Perm
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p1:RubiksSuperType := {
        fst := {
          permute := 1
          orient := 0
        }
        snd := {
          permute := p1
          orient := 0
        }
      }
      -- x 和 rubiks_p1 是一回事：
      have x_eq_rubiks_p1: x = rubiks_p1
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        sorry
      let solution := (G3Perm)
      have Solution_mul_rubiksp1_isOne: rubiks_p1 * solution = 1
        := by
        simp only [rubiks_p1]
        simp only [List.formPerm_cons_cons]
        -- [0,3,1] ↔ {0=>3,3=>1,1=>0} ↔  (a→c→b)
        -- swap 0 3 ↔ {0=>3,3=>0} ↔ (a→ c→ a)
        -- [3,1] ↔ {3=>1,1=>3,0=>0} ↔ (b→ c→ b)
        simp only [List.formPerm_singleton]
        simp only [mul_one]
        rw [← Solved_eq_1,lemma32_001]
        simp only [List.formPerm_cons_cons]
        simp only [List.formPerm_singleton]
        simp only [mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p1]
        have R_rubiksp1_mul_Solution: Reachable (rubiks_p1 * solution) := by
          rw [Solution_mul_rubiksp1_isOne];
          exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p1) (solution) R_rubiksp1_mul_Solution
        apply testaaa1
        sorry
    }
    by_cases ha2:x.2.permute = p2
      -- 执行：
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p2:RubiksSuperType := {
        fst := {
          permute := 1
          orient := 0
        }
        snd := {
          permute := p2
          orient := 0
        }
      }
      -- x 和 rubiks_p2 是一回事：
      have x_eq_rubiks_p2: x = rubiks_p2
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        sorry
      let solution := conjugate_formula (U*L2*U'*L2) (conjugate_formula (F') G3Perm)
      -- g3:R U' R U R U R U' R' U' R R
      --           σ(g3) =(1,2,4)
      -- 找一个替代解法，先搞一个(2,4,6): F' g3 F : F' R U' R U R U R U' R' U' R R F
      -- 舞台上必须站着1
      -- 然后：:U L L U' L L (2,4,6) L L U L L U' = (1,2,6)
      have Solution_mul_rubiksp2_isOne: rubiks_p2 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma32_002]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p2]
        have R_rubiksp2_mul_Solution: Reachable (rubiks_p2 * solution) := by
          rw [Solution_mul_rubiksp2_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p2) (solution) R_rubiksp2_mul_Solution
        apply testaaa1
        sorry
    }
    by_cases ha3:x.2.permute = p3
      -- 执行：
      -- 即可完成。此时制造一个RubiksSuperType
    {
      let rubiks_p3:RubiksSuperType := {
        fst := {
          permute := 1
          orient := 0
        }
        snd := {
          permute := p3
          orient := 0
        }
      }
      -- x 和 rubiks_p3 是一回事：
      have x_eq_rubiks_p3: x = rubiks_p3
        := by
        simp only [mul_one]
        simp only [← h2,← h3,← h4]
        -- simp [ha0,p3,h2,h3,h4]
        sorry
      let solution := (conjugate_formula (U2*L2*U2) (conjugate_formula B (VariantFaceTurn_R_List G3Perm_List)))
      -- 换一种解法：现有(1,2,3) : G3Perm 的R变式。VariantFaceTurn_R_List G3Perm_List
      -- 然后得到：(1,2,7): B (1,2,3) B' : B R R U' F F R R F F U U F F R R F F U' R R B'
      -- 然后得到：（1，7，12）：U2 L2 U2 (1,2,7) U2 L2 U2 : 替换成功
      have Solution_mul_rubiksp3_isOne: rubiks_p3 * solution = 1
        := by
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
        rw [← Solved_eq_1,lemma32_003]
        simp only [List.formPerm_cons_cons, List.formPerm_singleton, mul_one]
      rw [x_eq_Solvedx]
      apply Reachable.mul
      · exact Reachable.Solved
      · rw [x_eq_rubiks_p3]
        have R_rubiksp3_mul_Solution: Reachable (rubiks_p3 * solution) := by
          rw [Solution_mul_rubiksp3_isOne];exact Reachable.Solved
        have testaaa1 := Reachable.split_fst (rubiks_p3) (solution) R_rubiksp3_mul_Solution
        apply testaaa1
        sorry
    }
    sorry




  -- 证明右推左的限制条件1意味着只需选这2种情况进行分类讨论。
  /-- 1.（奇X奇) 2.(偶X偶）-/
  lemma lemma12_condition1_restriction
  (x:RubiksSuperType)
  -- (h1:x ∈ ValidCube)
  :sign x.1.permute = sign x.2.permute
  ↔
  (sign x.1.permute = -1 ∧ -1 = sign x.2.permute)
  ∨
  (sign x.1.permute = 1 ∧ 1 = sign x.2.permute)
  := by
    constructor
    · intro signEq
      by_cases ha0:(sign x.1.permute = -1)
      { left
        simp only [ha0,← signEq]
        simp only [and_self]
      }
      {
        have ha1:(sign x.1.permute = 1)
          := by
          sorry
        right
        simp only [ha1,← signEq]
        simp only [and_self]
      }
    · intro oneOrNegone
      cases' oneOrNegone with BothNegone BothOne
      · simp only [BothNegone]
      · simp only [BothOne]
    done


  -- 对于任意g状态角块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的角块位置置换变成1，而且保持(g*x1)的棱块位置不变，而且所有块的方向数不变。
    -- 这里x1的例子我们使用3循环的复合。
  lemma lemma14
  (g:RubiksSuperType)
  -- 1. g.1.p 是偶的置换
  (h1:g.1.permute ∈ alternatingGroup (Fin 8))
  :exist_reachableG_cornerPermute_to1 g
  := by
    -- 2.lemma31,lemma32:即所有满足这样的g:RubiksSuperType：
      -- {1.IsThreeCycle g.1.p ；2.g.1.o = 0 ；3.g.2.p=1 ; 4.g.2.o=0 }
      -- 都能通过群G复合生成。
    -- 3. 由于g.1.p 是偶的置换，使用这里面应该用到了closure_three_cycles_eq_alternating
      -- g.1.p 可以表示成3循环的乘积,这里记为threeList
    have h2 : ∃ (threeList:List (Perm (Fin 8))) ,
      (∀ a ∈ threeList, IsThreeCycle a)
      ∧
      (g.1.permute = threeList.prod)
      := by
      -- 可能要用归纳法证明。将偶置换表示成一长串3循环的乘积。
      sorry
    obtain ⟨permList,h2_2,h2_3⟩ := h2
    -- 4. 此处需要一个引理alternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one来带入这个结论
      -- g可以表示成若干RubiksSuperType和一个rst1:RubiksSuperType的乘积，这里记为rubiksList.
      -- rubiksList满足：{对所有元素a，IsThreeCycle a.1.p；a.1.orient=0; a.2.permute=1; a.2.orient=0}
      -- rst1满足：{a.1.p = 1 ; a.1.orient=g.1.orient; a.2.permute=g.2.permute ; a.2.orient=g.2.orient}
    have h3 := alternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
      g permList h2_2 h2_3
    obtain ⟨rubiksList,rst1,g_split,h3_4,unChanged3,h3_6⟩ := h3
    -- 5.总结：命题所需的复合操作就是(rubiksList.prod)⁻¹
    simp only [exist_reachableG_cornerPermute_to1]
    use (rubiksList.prod)⁻¹
    have rubiksListElement_3items_is0or1 :∀b ∈ rubiksList, b.1.orient=0 ∧ b.2.permute=1 ∧ b.2.orient=0
      := by
      simp only [Prod.forall]
      simp only [h3_6]
      intro i1 i2 i3
      simp at i3
      simp only [permFin8_to_RubiksSuperType] at i3
      simp at i3
      obtain ⟨i4,i5,i6,i7⟩ := i3
      apply And.intro
      { rw [← i6]}
      apply And.intro
      { rw [← i7]}
      { rw [← i7]}
    have rubiksListElement_permuteIsThreeCycle :∀b ∈ rubiksList, IsThreeCycle b.1.permute
      := by
      simp only [Prod.forall]
      simp only [h3_6]
      intro i1 i2 i3
      simp at i3
      simp only [permFin8_to_RubiksSuperType] at i3
      simp at i3
      obtain ⟨i4,i5,i6,i7⟩ := i3
      rw [← i6]
      simp
      exact h2_2 i4 i5
    apply And.intro
    · have rubiksListElement_isReachable: ∀b ∈ rubiksList, Reachable b
        := by
        intro b binL
        have app1 := rubiksListElement_3items_is0or1 b binL
        have app2 := rubiksListElement_permuteIsThreeCycle b binL
        apply lemma31
        · exact app2
        simp only [app1];simp only [app1];simp only [app1]
      apply Reachable.inv
      -- simp [Reachable.mul,rubiksListElement_isReachable]
      -- 很明显了
      sorry
    rw [g_split]
    simp only [mul_inv_cancel_right]
    apply And.intro
    · exact h3_4
    rw [← g_split]
    apply And.intro
    · exact unChanged3.1.symm
    apply And.intro
    · exact unChanged3.2.2.symm
    · exact unChanged3.2.1.symm
    done


  -- 对于任意g状态棱块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的棱块位置置换变成1，而且保持(g*x1)的角块位置不变，而且所有块的方向数不变。
    -- 这里x1的例子我们使用3循环的复合。
  lemma lemma15
  (g:RubiksSuperType)
  (h1:g.2.permute ∈ alternatingGroup (Fin 12))
  :exist_reachableG_edgePermute_to1 g
  := by
    -- 2.lemma31,lemma32:即所有满足这样的g:RubiksSuperType：
      -- {1.IsThreeCycle g.1.p ；2.g.1.o = 0 ；3.g.2.p=1 ; 4.g.2.o=0 }
      -- 都能通过群G复合生成。
    -- 3. 由于g.1.p 是偶的置换，使用这里面应该用到了closure_three_cycles_eq_alternating
      -- g.1.p 可以表示成3循环的乘积,这里记为threeList
    have h2 : ∃ (threeList:List (Perm (Fin 12))) ,
      (∀ g ∈ threeList, IsThreeCycle g)
      ∧
      (g.2.permute = threeList.prod)
      := by
      --可能要用归纳法证明。将偶置换表示成一长串3循环的乘积。
      sorry
    obtain ⟨permList,h2_2,h2_3⟩ := h2
    -- 4. 此处需要一个引理alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one来带入这个结论
      -- g可以表示成若干RubiksSuperType和一个rst1:RubiksSuperType的乘积，这里记为rubiksList.
      -- rubiksList满足：{对所有元素a，IsThreeCycle a.1.p；a.1.orient=0; a.2.permute=1; a.2.orient=0}
      -- rst1满足：{a.1.p = 1 ; a.1.orient=g.1.orient; a.2.permute=g.2.permute ; a.2.orient=g.2.orient}
    have h3 := alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one
      g permList h2_2 h2_3
    obtain ⟨rubiksList,rst1,g_split,h3_4,unChanged3,h3_6⟩ := h3
    -- 5.总结：命题所需的复合操作就是(rubiksList.prod)⁻¹
    simp only [exist_reachableG_edgePermute_to1]
    use (rubiksList.prod)⁻¹
    have rubiksListElement_3items_is0or1 :∀b ∈ rubiksList, b.1.orient=0 ∧ b.1.permute=1 ∧ b.2.orient=0
      := by
      simp only [Prod.forall,h3_6]
      sorry
    have rubiksListElement_permuteIsThreeCycle :∀b ∈ rubiksList, IsThreeCycle b.2.permute
      := by
      sorry
    apply And.intro
    · have rubiksListElement_isReachable: ∀b ∈ rubiksList, Reachable b
        := by
        intro b binL
        have app1 := rubiksListElement_3items_is0or1 b binL
        have app2 := rubiksListElement_permuteIsThreeCycle b binL
        apply lemma32
        · exact rubiksListElement_permuteIsThreeCycle b binL
        simp only [app1];simp only [app1];simp only [app1]
      apply Reachable.inv
      sorry
    rw [g_split]
    simp only [mul_inv_cancel_right]
    apply And.intro
    · exact h3_4
    rw [← g_split]
    apply And.intro
    · exact unChanged3.1.symm
    apply And.intro
    · exact unChanged3.2.2.symm
    · exact unChanged3.2.1.symm
    done

  -- 就是lemma14+15的简单结合
  -- 对于任意g状态角块位置置换属于偶置换的状态，且棱块位置置换属于偶置换的状态，
    -- 则存在操作x1使得(g*x1)的棱块位置置换变成1，而且角块位置置换变成1，而且所有块的方向数不变。
  lemma lemma16
  (g:RubiksSuperType)
  (h1:g.1.permute ∈ alternatingGroup (Fin 8))
  (h2:g.2.permute ∈ alternatingGroup (Fin 12))
  :∃ x1 : RubiksSuperType,
  Reachable x1
  ∧
  ((g*x1).1.permute = 1 ∧ (g*x1).2.permute = 1)
  ∧
  ((g*x1).1.orient = (g).1.orient ∧ (g*x1).2.orient = (g).2.orient )
  := by
    have cornerPermuteTo1 := lemma14 g h1
    obtain ⟨c1,c2,c3,c4,c5,c6⟩ := cornerPermuteTo1
    have EdgePermute_remains_in_aGroup: (g * c1).2.permute ∈ alternatingGroup (Fin 12)
      := by
      rw [c6]
      exact h2
    have edgePermuteTo1 := lemma15 (g * c1) EdgePermute_remains_in_aGroup
    obtain ⟨e1,e2,e3,e4,e5,e6⟩ := edgePermuteTo1
    use (c1 * e1)
    apply And.intro
    · apply Reachable.mul
      {exact c2}
      {exact e2}
    apply And.intro
    · apply And.intro
      · rw [← mul_assoc,e6,c3]-- e6 c3
      · rw [← mul_assoc,e3] -- e3
    · exact
      {left := by rw [← mul_assoc,e4,c4]
       right := by rw [← mul_assoc,e5,c5]}
    done

  -- 所有lemma12_condition1_restriction中的情况1可以通过魔方群操作变成情况2，sign都是1。
  /-- （奇X奇) → (偶X偶）-/
  lemma oddXoddToEvenXEven
  (x: RubiksSuperType)
  (h3: (sign x.1.permute = -1 ∧ -1 = sign x.2.permute) )
  :
  ∃ (g: RubiksSuperType), -- 要找到一个定理是permute作用一个2轮换后，奇偶性会变换1次的。,举例操作是g5
    Reachable g
    ∧
    (sign (x * g).1.permute = 1 ∧ 1 = sign (x * g).2.permute)
  := by
    sorry

  --sign都是1的魔方可达
  theorem EvenPermute_valid_isReachable
  (x: RubiksSuperType)
  (h3_2: sign x.1.permute = 1 ∧ 1 = sign x.2.permute)
  (hvx: x ∈ ValidCube)
  :Reachable x
  := by
    have xIsValid := hvx -- 后面被拆散了，先保留一个。
    simp [ValidCube] at hvx
    let currStat := x
    -- 分类讨论1得到小引理1：假设有状态g∈H,且∑(8在上 i=1) vi(g) = 0 (mod 3),则=>, g能通过有限次作用G中的元素，得到新的性质：v(g)={0,0,...,0}。而且不改变棱块的方向数。
    have h1 := lemma1 x hvx.2.1
    obtain ⟨h1_2,h1_3,h1_4,h1_5,h1_6,h1_7⟩ := h1
    let currStat := x * h1_2
    let currStat_satisfy := h1_4
    -- 分类讨论2得到小引理2:假设有状态g∈H,且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,g能通过有限次作用G中的元素，得到新的性质：w(g)={0,0,...,0}。并且不改变角块的方向数。
    have h2 := lemma2 (x * h1_2)
    have h2_2 := hvx.2.2
    rw [h1_5] at h2_2
    have h2 := lemma2 (x * h1_2) h2_2
    obtain ⟨h2_3,h2_4,h2_5,h2_6,h2_7,h2_8⟩ := h2
    have h2_9 := h1_4
    rw [h2_6] at h2_9
    let currStat := x * h1_2 * h2_3
    let currStat_satisfy: ((x * h1_2 * h2_3).2.orient = 0) ∧ ((x * h1_2 * h2_3).1.orient = 0)
      := { left := h2_5, right := h2_9 }
    -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
    have h3 := hvx.1
    rw [lemma12_condition1_restriction] at h3
    -- //
    have h3_2_1 : (x * h1_2 * h2_3).1.permute ∈ alternatingGroup (Fin 8)
      := by
      rw [h2_7.1.symm,h1_6.1.symm]
      apply mem_alternatingGroup.2
      exact h3_2.1
    have h3_2_2 : (x * h1_2 * h2_3).2.permute ∈ alternatingGroup (Fin 12)
      := by
      rw [h2_7.2.symm,h1_6.2.symm]
      apply mem_alternatingGroup.2
      exact h3_2.2.symm
    -- 使用lemma16使得新状态保持旧属性：方向数不变，获取新属性：角块+棱块的位置都变成1。
    have h3_2_3 := lemma16 (x * h1_2 * h2_3) h3_2_1 h3_2_2
    -- 很明显新状态就是还原状态Solved了，也就是已知下面这个y。
    obtain ⟨h3_2_4,h3_2_5,h3_2_6,h3_2_7,h3_2_8⟩ := h3_2_3
    obtain ⟨h3_2_9,h3_2_10⟩ := h3_2_6
    rw [h2_5] at h3_2_8
    rw [h2_9] at h3_2_7
    let currStat := x * h1_2 * h2_3 * h3_2_4
    let currStat_satisfy: (x * h1_2 * h2_3 * h3_2_4).1.orient = 0 ∧ (x * h1_2 * h2_3 * h3_2_4).2.orient = 0
    ∧ (x * h1_2 * h2_3 * h3_2_4).1.permute = 1 ∧ (x * h1_2 * h2_3 * h3_2_4).2.permute = 1 :=
    {
      left := h3_2_7
      right := {
        left := h3_2_8
        right := {
          left := h3_2_9
          right := h3_2_10
        }
      }
    }
    -- 所以还需要证明Reachable y即可。很明显因为都是G里面的6个元素之一FaceTurn，肯定是Reachable。
    -- 将目标Reachable x变成  ∃ y, (Reachable y) ∧ (x * y = Solved)
    -- x经过有限次操作变成了y， y就是复原状态e。
    let y : RubiksSuperType := h1_2 * h2_3 * h3_2_4
    have h101 : Reachable y
      := by
      apply Reachable.mul
      · apply Reachable.mul
        · exact h1_7
        · exact h2_8
      · exact h3_2_5
    have h102 : x * y = Solved
      := by
      simp only [y]
      have h102_1 := Solved_iff (x * h1_2 * h2_3 * h3_2_4)
      rw [← mul_assoc]
      rw [← mul_assoc]
      have hh : x * h1_2 * h2_3 * h3_2_4 = (x * h1_2 * h2_3 * h3_2_4)
      := by exact rfl
      rw [hh]
      simp only [RubiksSuperType]
      symm
      apply h102_1.2
      apply And.intro
      {exact h3_2_9}
      apply And.intro
      {exact h3_2_10}
      apply And.intro
      {exact h3_2_7}
      {exact h3_2_8}
    have Reachable_xy: Reachable (x*y)
      := by
      rw [h102]
      exact Reachable.Solved
    apply Reachable.split_fst x y Reachable_xy h101
    done


-- 右推左部分的证明blueprint：
-- valid_reachable = lemma1 + lemma2 + lemma12_condition1_restriction
              -- + oddXoddToEvenXEven + EvenPermute_valid_isReachable
-- 其中：
-- lemma1=lemma1_001_UFL+lemma1_002_DFL+lemma1_003_DFR+ ... + lemma1_007_UFR_and008DBL
-- lemma2=lemma2_001_UR+lemma2_002_FR+lemma2_003_RD+ ... +lemma2_011_UL_and_012_UF
-- EvenPermute_valid_isReachable = lemma1 + lemma2 + lemma12_condition1_restriction
                            --  + lemma16
-- lemma16 = lemma14 + lemma15
-- lemma14 = alternatingCornerPermute_eq_3Cycles_to_g_eq_3Cycles_mul_one + lemma31
-- lemma15 = alternatingEdgePermute_eq_3Cycles_to_g_eq_3Cycles_mul_one + lemma32


/-- 魔方基本定理的右推左部分：-/
theorem valid_reachable
: ∀x : RubiksSuperType, x ∈ ValidCube → Reachable x
:= by
  intro x hvx
  have xIsValid := hvx -- 后面被拆散了，先保留一个。
  simp only [ValidCube] at hvx
  let currStat := x
  -- 分类讨论1得到小引理1：假设有状态g∈H,且∑(8在上 i=1) vi(g) = 0 (mod 3),则=>, g能通过有限次作用G中的元素，得到新的性质：v(g)={0,0,...,0}。而且不改变棱块的方向数。
  have h1 := lemma1 x hvx.2.1
  obtain ⟨lemma1Move,h1_3,h1_4,h1_5,h1_6,h1_7⟩ := h1
  let currStat := x * lemma1Move
  let currStat_satisfy := h1_4
  -- 分类讨论2得到小引理2:假设有状态g∈H,且∑(12在上 i=1) wi(g) = 0 (mod 2) ， 则=>,g能通过有限次作用G中的元素，得到新的性质：w(g)={0,0,...,0}。并且不改变角块的方向数。
  -- have h2 := lemma2 (x * lemma1Move)
  have h2_2 := hvx.2.2
  rw [h1_5] at h2_2
  have h2 := lemma2 (x * lemma1Move) h2_2
  obtain ⟨lemma2Move,h2_4,h2_5,h2_6,h2_7,h2_8⟩ := h2
  have h2_9 := currStat_satisfy
  rw [h2_6] at h2_9
  let currStat := x * lemma1Move * lemma2Move
  let currStat_satisfy: ((x * lemma1Move * lemma2Move).2.orient = 0) ∧ ((x * lemma1Move * lemma2Move).1.orient = 0)
    := { left := h2_5, right := h2_9 }
  -- ValidCube的条件1，限制了当前状态x的范围，所以可以进行2种分类讨论：1.（奇X奇) 2.(偶X偶）
  have h3 := hvx.1
  rw [lemma12_condition1_restriction] at h3
  have cornerpermute_Remains : (x * lemma1Move * lemma2Move).1.permute = x.1.permute := by
    simp only [h2_7,h1_6]
  have edgepermute_Remains : (x * lemma1Move * lemma2Move).2.permute = x.2.permute := by
    simp only [h2_7,h1_6]
  have corner_eqPermuteSign_edge : sign (x * lemma1Move * lemma2Move).1.permute
  = sign (x * lemma1Move * lemma2Move).2.permute := by
    simp only [cornerpermute_Remains,edgepermute_Remains,hvx.1]
  cases h3 with
  | inl h3_1 =>
    -- 某个过程，存在一个复合操作，作用一次到状态集合（奇X奇)上的某个元素后，
    -- 新状态会属于新的状态集合(偶X偶）
    have h3_1_1 := oddXoddToEvenXEven x h3_1
    obtain ⟨OddToEvenMove,od2,od3,od4⟩ := h3_1_1
    have h3_1_2_1: x * OddToEvenMove  ∈ ValidCube := by
      apply RubiksGroup.mul_mem'
      · exact hvx
      · exact reachable_valid OddToEvenMove od2
    have h3_1_2: Reachable (x * OddToEvenMove) := EvenPermute_valid_isReachable (x * OddToEvenMove)
      {left:= od3 ,right:=od4} h3_1_2_1
    apply Reachable.split_fst
    · exact h3_1_2
    · exact od2
  | inr h3_2 =>
    apply EvenPermute_valid_isReachable
    · exact h3_2
    · exact hvx
    done
  done



/-- 魔方基本定理 -/
theorem RubikCube_BasicRule_2
: ∀x : RubiksSuperType, Reachable x ↔ x ∈ ValidCube
:= by
  intro h
  constructor
  · exact reachable_valid h
  · exact valid_reachable h
  done



end RubikCube_BasicRule_2
