import Lean
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Module.Equiv

-- set_option maxHeartbeats 800000
set_option maxRecDepth 4000


open Equiv Perm
open BigOperators
--本文件搭建了魔方超群和满足魔方基本定理条件的魔方子群（并证明它们是群和它们的运算定理）
--然后定义魔方的各种操作UDLRFB及可复原的状态Reachable
section RubiksSuperGroup

--将小于n的自然数置换并打印，同时定义相等的判断
  instance (n : Nat) : Repr (Perm (Fin n)) :=
    ⟨reprPrec ∘ Equiv.toFun⟩


  instance (n : Nat) : DecidableEq (Perm (Fin n)) := inferInstance

  /-- 可以看成全体角块，或全体棱块。-/
  --PieceState包含对每个块的置换信息和朝向改变信息
  structure PieceState (pieces orientations: ℕ+) where
    permute : Perm (Fin pieces)
    orient : Fin pieces → Fin orientations -- 这里是增加量，不是绝对量

    deriving Repr, DecidableEq


  def ps_mul {p o : ℕ+} -- 复合操作，也即定义置换和朝向改变的乘法
  : PieceState p o → PieceState p o → PieceState p o
  :=
    fun a1 a2 => {
      permute := a2.permute * a1.permute -- *先映射右，再映射左。
      --对于朝向，书上的公式是ρ(g)^(-1)·v(h) + v(g)，把项置换后输入索引等价于把索引置换后
      --输入新索引（但是置换顺序正好倒过来）
      --故ρ(g)^(-1)·v(h) + v(g)=(a2.orient ∘ a1.permute) + a1.orient
      orient := (a2.orient ∘ a1.permute) + a1.orient -- 复合函数计算顺序:右→左
    }


  -- 定义了PieceState的其中一种2元乘法运算。
  instance {p o : ℕ+} : Mul (PieceState p o) where
    mul a1 a2 := {
      permute := a2.permute * a1.permute
      orient := (a2.orient ∘ a1.permute) + a1.orient
    }


  -- 这里证明定理，从而能写*来代替ps_mul
  /-- 先“PieceState乘”后p = 先p后“PieceState乘” -/
  @[simp]
  theorem permute_mul {p o : ℕ+} (a1 a2 : PieceState p o)
  : (a1 * a2).permute = a2.permute * a1.permute
  := by rfl
  @[simp]
  theorem orient_mul {p o : ℕ+} (a1 a2 : PieceState p o)
  : (a1 * a2).orient = (a2.orient ∘ a1.permute) + a1.orient
  := by rfl

-- #check PieceState.mk.injEq

  /-- PieceState乘法的结合律 -/
  @[simp]
  lemma ps_mul_assoc {p o : ℕ+} :
  ∀ (a b c : PieceState p o),
  ps_mul (ps_mul a b) c = ps_mul a (ps_mul b c)
  := by
    intro a b c
    rw [ps_mul,ps_mul,ps_mul,ps_mul]
    -- simp only [ps_mul]
    simp only [PieceState.mk.injEq] -- ***两同类型对象相等，等价于，各分量相等。
    apply And.intro
    · rw [Perm.mul_def,Perm.mul_def,Perm.mul_def,Perm.mul_def]
      -- simp only [Perm.mul_def]
      ext i
      rw [trans_apply]
      rw [trans_apply]
      rw [trans_apply]
      rw [trans_apply]
    · simp only [coe_mul] -- 乘法号 和 复合符号 效果是一样的。
      rw [← add_assoc]
      simp only [add_left_inj]
      ext i
      simp only [Pi.add_apply]
      simp only [Function.comp_apply] -- 去掉复合符号
      simp only [Pi.add_apply]
      simp only [Function.comp_apply]
    done

  /-- PieceState乘法的左单位元 是{permute := 1, orient := 0}-/
  @[simp]
  lemma ps_one_mul {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul {permute := 1, orient := 0} a = a
  := by
    intro a
    simp only [ps_mul]
    simp only [mul_one]
    simp only [coe_one, Function.comp_id, add_zero]
    done

  /-- PieceState乘法的右单位元 也是{permute := 1, orient := 0}-/
  @[simp]
  lemma ps_mul_one {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul a {permute := 1, orient := 0} = a := by
    intro a
    simp only [ps_mul]
    simp only [one_mul, one_symm, coe_one, Function.comp_id, add_zero]
    simp only [Pi.zero_comp, zero_add]
    done


  /-- 定义PieceState乘法的普通元素的右逆表达式 -/
  def ps_inv {p o : ℕ+}
  : PieceState p o → PieceState p o
  :=
    fun A =>
    {
      permute := A.permute⁻¹
      orient := fun x => (- A.orient) (A.permute⁻¹ x)
    }

  /- 证明右逆的定义合理：-/
  @[simp]
  lemma ps_mul_right_inv {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul a (ps_inv a)  = {permute := 1, orient := 0}
  := by
    intro a
    simp only [ps_mul]
    simp only [ps_inv]
    simp only [mul_left_inv]
    simp only [Pi.neg_apply]
    simp only [PieceState.mk.injEq]
    simp only [true_and]
    ext i
    simp only [Pi.add_apply]
    simp only [Function.comp_apply]
    simp only [inv_apply_self]
    simp only [add_left_neg]
    simp only [Fin.val_zero']
    simp only [Pi.zero_apply]
    simp only [Fin.val_zero']
    done

  -- 类似Mul， 右逆元素简写成符号“-1”。
  instance {p o : ℕ+} : Neg (PieceState p o) where
    neg := fun
      | .mk permute orient => {
        permute := permute⁻¹
        orient := fun x => (- orient) (permute⁻¹ x)
      }


  -- 定义右的逆后，证明右的逆，左乘也为1：
  @[simp]
  lemma ps_mul_left_inv {p o : ℕ+} :
  ∀ (a : PieceState p o),
  ps_mul (ps_inv a) a = {permute := 1, orient := 0}
  := by
    intro a
    simp only [ps_inv]
    simp only [ps_mul]
    simp only [PieceState.mk.injEq]
    simp only [Pi.neg_apply]
    simp only [mul_right_inv]
    simp only [true_and]
    apply neg_eq_iff_add_eq_zero.1
    ext i
    simp only [Pi.neg_apply]
    simp only [Function.comp_apply]


  /-- 上述证明得到一个由角块（棱块）状态组成的群。包括有可能是魔方正常操作不能到达的状态。 -/
  instance PieceGroup (p o: ℕ+) :
  Group (PieceState p o) := {
    mul := ps_mul -- 提供一种PieceState的二元乘法运算，这里提供了ps_mul。
    mul_assoc := ps_mul_assoc -- 证明：上面乘法的结合律
    one := {permute := 1, orient := 0} -- 提供一种乘法运算的单位1
    one_mul := ps_one_mul -- 证明：上面的单位1左乘任意元素不变
    mul_one := ps_mul_one -- 证明：上面的单位1右乘任意元素不变
    inv := ps_inv -- 提供一个函数，输入一个PieceState对象，得到一个PieceState的逆对象。
    mul_left_inv := ps_mul_left_inv -- 证明:上面生成逆对象的函数生成的逆对象，左乘原对象结果为1
  }

  --定义简化运算符
  @[simp]
  lemma PieceState.mul_def {p o : ℕ+} (a b : PieceState p o)
  : a * b  = ps_mul a b := by rfl
  @[simp]
  lemma PieceState.inv_def {p o : ℕ+} (a b : PieceState p o)
  : a⁻¹ = ps_inv a := by rfl

  --固定角块和棱块的状态参数
  abbrev CornerType := PieceState 8 3
  abbrev EdgeType := PieceState 12 2

  -- PieceGroup 输入任意2个值都可以形成一个群。并且满足结合律，左逆等。

  instance RubiksCornerGroup :
  Group CornerType
  := PieceGroup 8 3
  instance RubiksEdgeGroup :
  Group EdgeType
  := PieceGroup 12 2

  /-- 角块和棱块的状态凑在一起，是魔方超群。 -/
  abbrev RubiksSuperType := CornerType × EdgeType

  @[simp]
  lemma RubiksSuperType_mul_assoc :--结合律
  ∀ (a b c : RubiksSuperType),
  a * b * c = a * (b * c)
  := by
    simp only [Prod.forall]
    simp only [Prod.mk_mul_mk]
    simp only [PieceState.mul_def]
    simp only [ps_mul_assoc]
    simp only [forall_const]
    done

  instance RubiksSuperGroup
  : Group RubiksSuperType
  := by exact Prod.instGroup -- 笛卡尔积元素组成的群

end RubiksSuperGroup

-- 下面为魔方的6个基本操作的定义做铺垫：

-- List.lookup用来匹配第一个分量，如果匹配到返回存在，还有该项的第二个分量：
-- #eval List.lookup 3 [(1, 2), (3, 4), (3, 5)] = some 4
-- #eval List.lookup 2 [(1, 2), (3, 4), (3, 5)] = none


/-- 为了方便定义每个操作的"方向数增加量"orient,然后定义的Orient： -/
def Orient
(p o : ℕ+)
(pairs : List ((Fin p) × (Fin o)))
: Fin p → Fin o :=
  fun i =>
    match pairs.lookup i with
    | some x => x
    | none => 0
-- 举例说明：
-- 比如为了创建这个向量：![1, 0, 2, 2, 0, 1, 0, 0]，这样输入参数。8项分量，每一项为Fin 3,即小于3。
-- #eval Orient 8 3 [(0, 1), (1, 0), (2, 2), (3, 2), (4, 0), (5, 1), (6, 0), (7, 0)] -- ![1, 0, 2, 2, 0, 1, 0, 0]


def Solved--表示角块和棱块的单位状况
: RubiksSuperType
where
  fst := {
    permute := 1
    orient := 0
  }
  snd := {
    permute := 1
    orient := 0
  }

@[simp]
lemma Solved_eq_1: Solved = 1 :=by rfl

@[simp]
lemma Solved_iff--当x各个分量都是单位状态时，一定是Solved
(x: RubiksSuperType)
:
(Solved = x)
↔
(x.1.permute=1 ∧ x.2.permute=1 ∧ x.1.orient=0 ∧ x.2.orient=0)
:= by
  constructor
  · simp only [Solved]
    intro x
    cases x
    apply And.intro
    { rfl}
    { apply And.intro
      {rfl}
      apply And.intro
      {rfl}
      {rfl}
    }
  · intro hx
    obtain ⟨hx1,hx2,hx3,hx4⟩:= hx
    simp only [Solved]
    congr
    {exact id hx1.symm}
    {exact id hx3.symm}
    {exact id hx2.symm}
    {exact id hx4.symm}
    done



section FACE_TURNS

  -- 为了方便定义每个操作的“位置变化”：排列permute,然后定义的这个东西：
  -- 用序列描述置换: List (Fin 8) := [0,3,2,1] -- 这样写得到的Perm意思是：
  -- -- [0,3,2,1]表示：0=>3；3=>2；2=>1；1=>0
  -- -- 整理后就是： [0=>3,1=>0,2=>1,3=>2]

  def cyclePieces {α : Type*} [DecidableEq α]
  : List α → Perm α
  := fun list =>  List.formPerm list




  -- 第1大括号"{}"内描述的是：角块
    -- permute描述的是位置变化，orient描述的是方向数变化，注意描述的是位置改变后原方块情形。
  -- 第2大括号"{}"内描述的是：棱块
    -- permute描述的是位置变化，orient描述的是方向数变化。

  -- 这里注释一下下面每个位置对应的块：
  --   ({ permute := ![UFL, UFR, UBR, UBL, DFL, DFR, DBR, DBL],
  --    orient := ![UFL, UFR, UBR, UBL, DFL, DFR, DBR, DBL] },
  --  { permute := ![UF, UR, UB, UL, FL, FR, RB, LB, FD, RD, BD, LD],
  --    orient := ![UF, UR, UB, UL, FL, FR, RB, LB, FD, RD, BD, LD] })

  def U : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0,3,2,1], orient := 0},
      -- 即：0=>3,3=>2,2=>1,1=>0
      -- 整理：[3,0,1,2,4,5,6,7]
      {permute := cyclePieces [0,3,2,1], orient := 0}
    ⟩
  def D : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [4, 5, 6, 7], orient := 0},
      {permute := cyclePieces [8, 9, 10, 11], orient := 0}
    ⟩
  def R : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [1,2,6,5], orient := Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]},
      {permute := cyclePieces [1, 6, 9, 5], orient := Orient 12 2 [(1,1 ), (5,1 ), (6,1 ), (9,1 )]}
    ⟩
  -- #eval Orient 8 3 [(1, 2), (2, 1), (5, 1), (6, 2)]
  def L : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0, 4, 7, 3], orient := Orient 8 3 [(0, 1), (3, 2), (4, 2), (7, 1)]},
      {permute := cyclePieces [3,4 ,11 ,7 ], orient := Orient 12 2 [(3, 1), (4,1 ), (7, 1), (11, 1)]}
    ⟩
  def F : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [0,1 ,5 ,4 ], orient := Orient 8 3 [(0, 2), (1, 1), (4, 1), (5, 2)]},
      {permute := cyclePieces [0, 5, 8, 4] , orient :=  Orient 12 2 [(0, 0), (4, 0), (5, 0), (8, 0)]}
    ⟩
  def B : RubiksSuperType :=
    ⟨
      {permute := cyclePieces [2, 3, 7,6 ], orient := Orient 8 3 [(2, 2), (3, 1), (6, 1), (7, 2)]},
      {permute := cyclePieces [2, 7, 10,6 ], orient := Orient 12 2 [(2, 0), (6, 0), (7, 0), (10, 0)]}
    ⟩


  def U2 := U^2
  def D2 := D^2
  def R2 := R^2
  def L2 := L^2
  def F2 := F^2
  def B2 := B^2
  def U' := U⁻¹
  def D' := D⁻¹
  def R' := R⁻¹
  def L' := L⁻¹
  def F' := F⁻¹
  def B' := B⁻¹



--以上描述的是方向增加量，还要描述当前索引位置N对应块的绝对方向数
  def Corner_Absolute_Orient
  : CornerType → Fin 8 → Fin 3
  := fun x p => x.orient (x.permute.invFun p)

  def Edge_Absolute_Orient
  : EdgeType → Fin 12 → Fin 2
  := fun x p => x.orient (x.permute.invFun p)

  -- #eval Corner_Absolute_Orient U.1
  -- #eval Edge_Absolute_Orient U.2
  -- #eval Corner_Absolute_Orient F.1

  /-- 定义了哪些是属于魔方常见操作，均属于faceturn-/
  inductive FaceTurn
  : RubiksSuperType → Prop where
    | U : FaceTurn U
    | D : FaceTurn D
    | R : FaceTurn R
    | L : FaceTurn L
    | F : FaceTurn F
    | B : FaceTurn B
    | U2 : FaceTurn U2
    | D2 : FaceTurn D2
    | R2 : FaceTurn R2
    | L2 : FaceTurn L2
    | F2 : FaceTurn F2
    | B2 : FaceTurn B2
    | U' : FaceTurn U'
    | D' : FaceTurn D'
    | R' : FaceTurn R'
    | L' : FaceTurn L'
    | F' : FaceTurn F'
    | B' : FaceTurn B'


  instance : ToString RubiksSuperType where
  toString : RubiksSuperType → String :=
    fun c =>
      if c = Solved then "Solved"
      else if c = U then "U"
      else if c = D then "D"
      else if c = R then "R"
      else if c = L then "L"
      else if c = F then "F"
      else if c = B then "B"
      else if c = U2 then "U, U"
      else if c = D2 then "D, D"
      else if c = R2 then "R, R"
      else if c = L2 then "L, L"
      else if c = F2 then "F, F"
      else if c = B2 then "B, B"
      else if c = U' then "U'"
      else if c = D' then "D'"
      else if c = R' then "R'"
      else if c = L' then "L'"
      else if c = F' then "F'"
      else if c = B' then "B'"
      else s!"{repr c}" -- 如果都不匹配的话，直接打印出permute，orient的结构体。repr的作用。

  -- #eval toString $ U
  -- #eval toString $ U2
  -- #eval toString $ U*F




end FACE_TURNS



def TPerm : RubiksSuperType
  := R * U * R' * U' * R' * F * R2 * U' * R' * U' * R * U * R' * F'
def AlteredYPerm : RubiksSuperType
  := R * U' * R' * U' * R * U * R' * F' * R * U * R' * U' * R' * F * R

-- #eval TPerm
-- #eval AlteredYPerm


-- 以下两个定义，形容两个不可能的魔方状态：只拧一次角块，还有只拧一次棱块,用以测试后面的代码。

def CornerTwist : RubiksSuperType
  := (
      {permute := 1, orient := (fun | 0 => 1 | _ => 0) },
      -- 这种是归纳定义的向量写法，只有0位置为1，“_”意思是其余的，其余为0。
      {permute := 1, orient := 0}
     )
def EdgeFlip : RubiksSuperType
  := (
      {permute := 1, orient := 0},
      {permute := 1, orient := (fun | 0 => 1 | _ => 0)}
     )


-- #eval EdgeFlip

section RubiksGroup

  -- 直接定义满足魔方基本定理条件的有效魔方
  /-- 关于魔方状态集合的非直觉定义。-/
  def ValidCube :
  Set RubiksSuperType
  :=
  -- 这样的一个集合：其中的任意元素c，c满足后面这些条件。
  {
    c |
      Perm.sign c.fst.permute = Perm.sign c.snd.permute
      -- c.fst指的是角块 , c.snd指的是棱块。1，2也行。--奇置换为-1，偶置换为1
      ∧
      Finset.sum ({0,1,2,3,4,5,6,7}:Finset (Fin 8)) c.fst.orient = 0
      ∧
      Finset.sum ({0,1,2,3,4,5,6,7,8,9,10,11}:Finset (Fin 12)) c.snd.orient = 0
  }

    -- 用于mul_mem'，inv_mem'的证明
    /-- 证明8个角块方向分量如果求和为0（模3），随意排列组合后，求和还是为0（模3）。 -/
    @[simp]
    lemma mul_mem'_permuteRemainsSum_2
    (apermute : Perm (Fin 8))
    (borient : (Fin 8) → Fin 3)
    (h2: Finset.sum {0, 1, 2,3,4,5,6,7} borient = 0)
    : (Finset.sum {0, 1, 2,3,4,5,6,7} fun x ↦ borient (apermute x)) = 0
    := by
      have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
      have sumEq2 : ∑ i : Fin 8, borient (apermute i)
        = ∑ x in {0, 1, 2,3,4,5,6,7}, borient (apermute x) := rfl
      rw [← sumEq2]
      clear sumEq2
      rw [h1]
      clear h1
      exact h2
      done

    -- 用于mul_mem'的证明
    /-- 证明12个棱块方向分量如果求和为0（模2），随意排列组合后，求和还是为0（模2）。 -/
    @[simp]
    lemma mul_mem'_permuteRemainsSum
    (apermute : Perm (Fin 12))
    (borient : (Fin 12) → Fin 2)
    (h2: Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} borient = 0)
    : (Finset.sum {0, 1, 2,3,4,5,6,7,8,9,10,11} fun x ↦ borient (apermute x)) = 0
    := by
      have h1:= Equiv.sum_comp apermute borient -- 常见错误：因为没有输入足够的参数 typeclass instance problem is stuck, it is often due to metavariables
      have sumEq2 : ∑ i : Fin 12, borient (apermute i)
        = ∑ x in {0, 1, 2,3,4,5,6,7,8,9,10,11}, borient (apermute x) := rfl
      rw [← sumEq2]
      clear sumEq2
      rw [h1]
      clear h1
      exact h2
      done


    lemma psmul0orientAction_orientRemainsSum --若g和g2是0，g*g2求和mod3还是0
    (g:RubiksSuperType)
    (g2:RubiksSuperType)
    (g2SumOrient: Finset.sum {0, 1, 2,3,4,5,6,7} g2.1.orient = 0)
    (gSumOrient: Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} g.1.orient = 0)
    :
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} (g * g2).1.orient = 0
    := by
      have temp: (g * g2).1.orient = (g.1 * g2.1).orient
      :=by rfl
        -- simp only [RubiksSuperType_mul_assoc,
        --   Prod.fst_mul, Prod.pow_fst, PieceState.mul_def]
      rw [temp]
      clear temp
      have temp2 (a1:CornerType)(a2:CornerType): (a1 * a2).orient = (a2.orient ∘ a1.permute) + a1.orient
        := by rfl
      have h1:= temp2 g.1 g2.1
      rw [h1]
      clear h1 temp2
      simp only [Pi.add_apply]
      simp only [Finset.sum_add_distrib]
      rw [gSumOrient,add_zero]
      clear gSumOrient
      apply mul_mem'_permuteRemainsSum_2 g.1.permute _ g2SumOrient

    lemma psmul0orientAction_orientRemainsSum_2 --若g和g2是0，g*g2求和mod2还是0
    (g:RubiksSuperType)
    (g2:RubiksSuperType)
    (g2SumOrient: Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} g2.2.orient = 0)
    (gSumOrient: Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} g.2.orient = 0)
    :
    Finset.sum {0, 1, 2, 3, 4, 5, 6, 7,8,9,10,11} (g * g2).2.orient = 0
    := by
      have temp: (g * g2).2.orient = (g.2 * g2.2).orient
      :=by rfl
        -- simp only [RubiksSuperType_mul_assoc,
        --   Prod.snd_mul, Prod.pow_fst, PieceState.mul_def]
      rw [temp]
      clear temp
      have temp2 (a1:EdgeType)(a2:EdgeType): (a1 * a2).orient = (a2.orient ∘ a1.permute) + a1.orient
        := by rfl
      have h1:= temp2 g.2 g2.2
      rw [h1]
      clear h1 temp2
      simp only [Pi.add_apply]
      simp only [Finset.sum_add_distrib]
      rw [gSumOrient,add_zero]
      apply mul_mem'_permuteRemainsSum g.2.permute _ g2SumOrient


    -- 例子：moveAction = (F * G1Perm * F')
    -- 这个引理应该更加一般性一点，A+B=C
    lemma mulActon_CornerAbsoluteOrient_OneIndex_is0 --下一个定理的特殊情况
    (g : RubiksSuperType)
    (moveAction : RubiksSuperType)
    (index: Fin 8)
    (hRemainsP: (g * moveAction).1.permute = g.1.permute)
    (ha1: Corner_Absolute_Orient g.1 index = 1) -- A
    (h_MoveAction: (moveAction).1.orient index = 2) -- B
    :
    (Corner_Absolute_Orient (g*moveAction).1 index) = 0 -- C
    := by
      have h1: (g.1.orient + moveAction.1.orient ∘ g.1.permute) (g.1.permute⁻¹ index)
      = g.1.orient (g.1.permute⁻¹ index) + moveAction.1.orient (index)
      := by
        simp only [Pi.add_apply]
        simp only [Function.comp_apply]
        simp [Corner_Absolute_Orient] at ha1
        have temp: g.1.permute⁻¹ = g.1.permute.symm := by exact rfl
        rw [temp]
        rw [ha1]
        simp only [apply_symm_apply]
        done
      simp only [Corner_Absolute_Orient] at ha1
      simp at ha1
      -- 关键引理证明2：先找出从ha1发掘出的这个索引有什么用。
      have h2: g.1.orient (g.1.permute⁻¹ index) + moveAction.1.orient (index)
        = 0
      := by
        simp only [Inv.inv]
        rw [ha1]
        rw [h_MoveAction]
        rfl
        done
      have _h2_1: (g.1.orient + moveAction.1.orient ∘ ⇑g.1.permute) (g.1.permute⁻¹ index)
        = 0 := h1.trans h2
      simp only [Corner_Absolute_Orient]
      rw [hRemainsP]
      have _h2_4: (g.1.orient + moveAction.1.orient ∘ g.1.permute) = (g * moveAction).1.orient
        := by
        have _h2_4_1 := PieceState.mul_def g.1 moveAction.1
        simp only [ps_mul] at _h2_4_1
        simp only [← Prod.fst_mul] at _h2_4_1
        rw [_h2_4_1]
        simp only [Prod.fst_mul]
        rw [add_comm]
        done
      rw [← _h2_4]
      exact _h2_1
      done


    lemma mulActon_CornerAbsoluteOrient_OneIndex_is0_2 --对于角块，如果置换是单位置换，原方向绝对值
    --是N1，增加值是N2，则新绝对值是N1+N2=N3
    (N1 N2 N3: Fin 3)
    (h1plus2is3: N1+N2=N3)
    (g : RubiksSuperType)
    (moveAction : RubiksSuperType)
    (index: Fin 8)
    (hRemainsP: (g * moveAction).1.permute = g.1.permute)
    (ha1: Corner_Absolute_Orient g.1 index = N1) -- A
    (h_MoveAction: (moveAction).1.orient index = N2) -- B
    :
    (Corner_Absolute_Orient (g*moveAction).1 index) = N3 -- C
    := by
      have h1: (g.1.orient + moveAction.1.orient ∘ g.1.permute) (g.1.permute⁻¹ index)
      = g.1.orient (g.1.permute⁻¹ index) + moveAction.1.orient (index)
      := by
        simp only [Pi.add_apply]
        simp only [Function.comp_apply]
        simp [Corner_Absolute_Orient] at ha1
        have temp: g.1.permute⁻¹ = g.1.permute.symm := by exact rfl
        rw [temp]
        rw [ha1]
        simp only [apply_symm_apply]
        done
      simp only [Corner_Absolute_Orient] at ha1
      simp at ha1
      -- 关键引理证明2：先找出从ha1发掘出的这个索引有什么用。
      have h2: g.1.orient (g.1.permute⁻¹ index) + moveAction.1.orient (index)
        = N3
      := by
        simp only [Inv.inv]
        rw [ha1]
        rw [h_MoveAction]
        exact h1plus2is3
        done
      have _h2_1: (g.1.orient + moveAction.1.orient ∘ ⇑g.1.permute) (g.1.permute⁻¹ index)
        = N3 := h1.trans h2
      simp only [Corner_Absolute_Orient]
      rw [hRemainsP]
      have _h2_4: (g.1.orient + moveAction.1.orient ∘ g.1.permute) = (g * moveAction).1.orient
        := by
        have _h2_4_1 := PieceState.mul_def g.1 moveAction.1
        simp only [ps_mul] at _h2_4_1
        simp only [← Prod.fst_mul] at _h2_4_1
        rw [_h2_4_1]
        simp only [Prod.fst_mul]
        rw [add_comm]
        done
      rw [← _h2_4]
      exact _h2_1
      done

    lemma mulActon_EdgeAbsoluteOrient_OneIndex_is0_2 --棱块的情形
    (N1 N2 N3: Fin 2)
    (h1plus2is3: N1+N2=N3)
    (g : RubiksSuperType)
    (moveAction : RubiksSuperType)
    (index: Fin 12)
    (hRemainsP: (g * moveAction).2.permute = g.2.permute)
    (ha1: Edge_Absolute_Orient g.2 index = N1) -- A
    (h_MoveAction: (moveAction).2.orient index = N2) -- B
    :
    (Edge_Absolute_Orient (g*moveAction).2 index) = N3 -- C
    := by
      have h1: (g.2.orient + moveAction.2.orient ∘ g.2.permute) (g.2.permute⁻¹ index)
      = g.2.orient (g.2.permute⁻¹ index) + moveAction.2.orient (index)
      := by
        simp only [Pi.add_apply]
        simp only [Function.comp_apply]
        simp [Edge_Absolute_Orient] at ha1
        have temp: g.2.permute⁻¹ = g.2.permute.symm := by exact rfl
        rw [temp]
        rw [ha1]
        simp only [apply_symm_apply]
        done
      simp only [Edge_Absolute_Orient] at ha1
      simp at ha1
      -- 关键引理证明2：先找出从ha1发掘出的这个索引有什么用。
      have h2: g.2.orient (g.2.permute⁻¹ index) + moveAction.2.orient (index)
        = N3
      := by
        simp only [Inv.inv]
        rw [ha1]
        rw [h_MoveAction]
        exact h1plus2is3
        done
      have _h2_1: (g.2.orient + moveAction.2.orient ∘ ⇑g.2.permute) (g.2.permute⁻¹ index)
        = N3 := h1.trans h2
      simp only [Edge_Absolute_Orient]
      rw [hRemainsP]
      have _h2_4: (g.2.orient + moveAction.2.orient ∘ g.2.permute) = (g * moveAction).2.orient
        := by
        have _h2_4_1 := PieceState.mul_def g.2 moveAction.2
        simp only [ps_mul] at _h2_4_1
        simp only [← Prod.snd_mul] at _h2_4_1
        rw [_h2_4_1]
        simp only [Prod.fst_mul]
        rw [add_comm]
        done
      rw [← _h2_4]
      exact _h2_1
      done





  --证明ValidCube是群，而且是RubiksSuperGroup的子群
  /--然后再分析如何与Reachable（可操作到达）联系起来。
    首先证明群所需的性质之一：封闭性  -/
  @[simp]
  theorem mul_mem' {a b : RubiksSuperType}
  : a ∈ ValidCube → b ∈ ValidCube → a * b ∈ ValidCube
  := by
    intro hav hbv
    simp only [ValidCube]
    apply And.intro
    { -- 1.符号不变：
      have h1 : sign a.1.permute = sign a.2.permute
        := by apply hav.left
      have h2 : sign b.1.permute = sign b.2.permute
        := by apply hbv.left
      simp only [Prod.fst_mul]
      simp only [PieceState.mul_def]
      simp only [Prod.snd_mul]
      simp only [PieceState.mul_def]
      simp only [ps_mul]
      simp only [map_mul] -- sign映射是同态的，简单举例.
      exact Mathlib.Tactic.LinearCombination.mul_pf h2 h1
    }
    apply And.intro
    {-- 乘积的角块方向数增加量orient各分量求和为0（mod 2）
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} a.1.orient = 0
        := by apply hav.right.left
      have h2 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} b.1.orient = 0
        := by apply hbv.right.left
      simp only [Prod.fst_mul]
      simp only [PieceState.mul_def]
      simp only [ps_mul]
      simp only [Pi.add_apply]
      simp only [Function.comp_apply]
      simp only [Finset.sum_add_distrib]
      rw [h1]
      clear h1
      simp only [add_zero]
      apply mul_mem'_permuteRemainsSum_2
      exact h2
    }
    {-- 乘积的棱块方向数增加量orient各分量求和为0（mod 3）
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8,9,10,11} a.2.orient = 0
        := by apply hav.right.right
      have h2 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8,9,10,11} b.2.orient = 0
        := by apply hbv.right.right
      simp only [Prod.snd_mul]
      simp only [PieceState.mul_def]
      simp only [ps_mul]
      simp only [Pi.add_apply]
      simp only [Function.comp_apply]
      simp only [Finset.sum_add_distrib]
      rw [h1]
      clear h1
      simp only [add_zero]
      apply mul_mem'_permuteRemainsSum
      exact h2
    }

  -- #eval (1: RubiksSuperType)
--   { permute := ![0, 1, 2, 3, 4, 5, 6, 7], orient := ![0, 0, 0, 0, 0, 0, 0, 0] },
--  { permute := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], orient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] })

  /-- 从这个定义ValidCube
    证明群所需的性质之一：父群中的单位元也在该子群中；换句话说，子群里有单位元。  -/
  @[simp]
  lemma one_mem'
  : 1 ∈ ValidCube
  := by
    simp only [ValidCube]
    apply And.intro
    { decide }
    apply And.intro
    { decide }
    { decide }




  /-- 从这个定义ValidCube
    证明群所需的性质之一：父群中的逆函数生成的元素也在该子群中；换句话说，子群中每个元素都有逆元素。  -/
  @[simp]
  theorem inv_mem' {x : RubiksSuperType}
  :x ∈ ValidCube
  →
  x⁻¹ ∈ ValidCube
  := by
    intro hxv
    simp only [ValidCube]
    simp only [Set.mem_setOf_eq]
    simp only [Prod.fst_inv]
    simp only [Prod.snd_inv]
    simp only [PieceState.inv_def]
    simp only [ps_inv]
    apply And.intro
    {
      simp only [map_inv] -- 举例
      have h1:= hxv.1
      rw [h1]
    }
    apply And.intro
    { have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7} x.1.orient = 0
        := by apply hxv.right.left
      apply mul_mem'_permuteRemainsSum_2
      simp only [Pi.neg_apply]
      simp only [Finset.sum_neg_distrib]
      simp only [neg_eq_zero]
      exact h1
    }
    {
      have h1 : Finset.sum {0, 1, 2, 3, 4, 5, 6, 7, 8,9,10,11} x.2.orient = 0
        := by apply hxv.right.right
      apply mul_mem'_permuteRemainsSum
      simp only [Pi.neg_apply]
      simp only [Finset.sum_neg_distrib]
      simp only [neg_eq_zero]
      exact h1
    }


  /-- ValidCube群所需的性质都准备好了，正式定义这个群  -/
  instance RubiksGroup : Subgroup RubiksSuperType := {
    carrier := ValidCube -- 提供一个RubiksSuperType群的子集合ValidCube。
    mul_mem' := mul_mem' -- 封闭性质
    one_mem' := one_mem' -- 单位1元素
    inv_mem' := inv_mem' -- 沿用父群的逆函数定义，需要证明这样定义产生的逆元素也在提供的子集合ValidCube中。
    -- 结合律的性质，父群已经证明。
    -- 左乘单位元=本身的性质，已经证明
    -- 右乘单位元=本身，已经证明
    -- 左乘逆函数产生的逆元=单位元，已经证明
    -- 右乘逆函数产生的逆元=单位元，已经证明
  }


  /-- 这个就是直觉的魔方状态集合定义，用六个操作作为生成元得到。后面将用一个定理证明这两个定义的集合是等价的。
   -/
  inductive Reachable
  : RubiksSuperType → Prop
  where
    | Solved : Reachable Solved -- 已还原状态"是Reachable的"
    -- 下面是3种方法，从定义上构造“xx是Reachable的”：
    | FT : ∀x : RubiksSuperType, FaceTurn x → Reachable x
    | mul : ∀x y : RubiksSuperType, Reachable x → Reachable y → Reachable (x * y)
    | inv :  ∀x : RubiksSuperType, Reachable x → Reachable x⁻¹

  /-- 从以上的4种基础定义，可以推出第5种基础定义：xy可达，y可达，那么x也可达。 -/
  def Reachable.split_fst: ∀x y : RubiksSuperType, Reachable (x * y) → Reachable y → Reachable x
  := by
    intro x y Rxy Ry
    have h1 := Reachable.inv (x * y) Rxy
    simp at h1 -- Reachable (y⁻¹ * x⁻¹) -- 想知道simp做了什么，可以用print，或者另开一个have。
      -- 这里简单举例说明：
      -- (x*y)⁻¹  = (y⁻¹ * x⁻¹) -- 这里应该是因为：左右同乘一个(x*y)来的
      -- 1 = 1 -- 是因为满足结合律，还有左逆，所以有这个推理。
    have h3 := Reachable.mul (y) (y⁻¹ * x⁻¹) Ry h1
    simp at h3
    have h4 := Reachable.inv (x⁻¹) h3
    simp at h4
    exact h4


  /-- 第6种基础定义: 同样xy可达，x可达，那么y也可达。-/
  def Reachable.split_snd: ∀x y : RubiksSuperType, Reachable (x * y) → Reachable x → Reachable y
  := by
    intro x y Rxy Rx
    have h1 := Reachable.inv (x * y) Rxy
    simp at h1 -- Reachable (y⁻¹ * x⁻¹)
    have h3 := Reachable.mul (y⁻¹ * x⁻¹) (x) h1 Rx
    simp at h3
    have h4 := Reachable.inv (y⁻¹) h3
    simp at h4
    exact h4



end RubiksGroup


section SolutionState

  def CornersSolved :
  RubiksSuperType → Prop
  :=
    fun c =>
      -- 定义需要满足：
      c.fst.permute = 1
      ∧
      c.fst.orient = 0

  def EdgesSolved
  : RubiksSuperType → Prop
  :=
    fun c =>
      -- 定义需要满足：
      c.snd.permute = 1
      ∧
      c.snd.orient = 0

  def IsSolved
  : RubiksSuperType → Prop
  :=
    fun c =>
      -- 定义需要满足：
      CornersSolved c
      ∧
      EdgesSolved c



end SolutionState
