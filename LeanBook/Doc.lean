/- # mvcgen を使って命令的プログラムの検証をする

> 元記事:
> <https://hackmd.io/@sg-fro/BJRlurP_xg>

`mvcgen` タクティックはモナディックな検証条件生成器 (monadic verification condition generator) を実装しています。
このタクティックは Lean の命令的な `do` 記法で書かれたプログラムを含むゴールを、純粋な検証条件の集合に分解して処理します。
ここでいう検証条件 (verification condition) とは、`do` ブロックの背後にあるモナドを一切参照しない部分ゴールのことです。
つまり、プログラムの命令的な部分を抽象化し、最終的にモナドに依存しない純粋な性質を証明すれば、もとのゴール全体も成立する、という仕組みです。

mvcgen への「Hello world」として、次の例では `mySum` がローカルな可変変数と `for` ループを使って配列の総和を計算します。
そのうえで、この `mySum` が `Array.sum` と同値であることを証明します。
その際には、ループに対して不変条件 (invariant) を明示的に指定する必要があります。
-/
import Std.Tactic.Do
import Lean

-- mvcgen はまだ使用しないでというwarningを消す
set_option mvcgen.warning false

/-- for文を使ってリストの和を計算する -/
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

open Std.Do

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- モナディックに実装されている（`Id.run do ...`）部分にフォーカスします
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- 検証条件に分解する
  mvcgen
  -- ループ全体を通して成り立たせたい不変条件を指定する
  -- * `out` は `let mut` で導入した変数の現在値を表します
  -- * `xs` は `List.Cursor` で，リストを接頭辞 `xs.prefix` と接尾辞 `xs.suffix` に
  --   分割して表すデータ構造です。どこまでループが進んだかを追跡します。
  --   つまり進捗（ループの到達位置）を記録します。
  -- 不変条件は「`out` が接頭辞の総和を保持している」ことです。
  -- 記法 ⌜p⌝ は，純粋な命題 `p : Prop` をアサーション言語に埋め込みます。
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- 不変条件を指定した後は，“証明モードを抜ける”ことでゴールをさらに簡約できます。
  -- `mleave` は安定した `simp` サブセットに対する `simp only [...] at *` の糖衣です。
  all_goals mleave
  -- 各反復で不変条件が保存されることを証明する
  case vc1.step ih =>
    -- ここでのゴールには `pref` が現れます。これは不変条件に渡されたカーソルの
    -- `prefix` フィールドを束縛したものです。依存型のカーソルを展開すると
    -- `grind` が働きやすくなります。
    grind
  -- ループ開始時に不変条件が成り立つことを証明する
  case vc2.a.pre =>
    grind
  -- ループ終了時の不変条件から目標の性質が従うことを証明する
  case vc3.a.post h =>
    grind

/-
ループ不変条件を指定したあとは、証明は `all_goals mleave; grind` だけにまで短縮できます。
なお、`case` ラベルには `vc1`、`vc2`、`vc3` などの一意なプレフィックスが付きます。
ケースを参照するときは、このプレフィックスだけを使うべきで、サフィックスはその検証条件（VC）がどこから来たかをユーザーに伝えるための簡易な手掛かりに過ぎません。

例えば:

* **`vc1.step`** は、この検証条件がループにおける帰納ステップ（不変条件が次の繰り返しでも保持されること）を証明するものであることを示しています。
* **`vc2.a.pre1`** は、与えられたゴールの仮定が `forIn` の仕様における事前条件を満たすことを証明するものです。
* **`vc3.a.post`** は、`forIn` の仕様における事後条件からゴールが目標とする性質が導かれることを証明するものです。

`mvcgen`を使用しない伝統的な正しさ証明（correctness proof）と比較してみると役に立ちます。
-/

theorem mySum_correct_traditional (l : Array Nat) : mySum l = l.sum := by
  -- 配列をリストに変換する
  cases l with | mk l =>
  -- `mySum` を展開し，`forIn` を `foldl` に書き換える
  simp [mySum]
  -- 帰納法の仮定を一般化する
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- grind で片づける
  induction l with grind

/-
この証明は、`mvcgen` を用いた証明と同様に簡潔です。
しかし、従来型の手法はプログラムの重要な性質に依存しています：

* `for` ループが途中で `break` したり早期に `return` したりしないこと。そうでないと、`forIn` を `foldl` に書き換えることはできません。
* ループ本体 `(· + ·)` が、証明の中で繰り返し展開しても扱える程度に小さいこと。
* ループ本体が純粋 (pure) であり、すなわち副作用 (effects) を伴わないこと。
  （実際、基底モナド `Id` の計算はすべて `pure` を介して表せます。）

`forIn` は `foldlM` へ書き換えること自体は可能ですが、モナディックなループ本体について推論するのは `grind` にとって骨が折れる場合があります。

以下のセクションでは、`mvcgen` とそのサポートライブラリを学ぶためにいくつかの例を順に見ていき、あわせて従来型の証明が難しくなる場面も確認します。これはたいてい次の理由で生じます。

* 早期 `return` を伴う（ネストした）`for` ループなどの制御フロー構文を用いる `do` ブロック。
* `Id` 以外のモナドにおける効果的（effectful）な計算。そのような計算は暗黙のモナディック文脈（状態・例外など）に影響を与え，その影響をループ不変条件に反映する必要がある。

`mvcgen` は、これらの課題に対しても合理的な労力でスケールします。
-/

/-
## control flow

for ループと早期 `return` を組み合わせた別の例を考えてみましょう。
`List.Nodup` は、与えられたリストが重複を含まないことを主張する述語であることを思い出してください。
以下の例の関数 `nodup` は、この述語を判定します。
-/

/-- リストに重複がないか判定する。
true なら重複がない。false なら重複がある。-/
def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 =>
    exact Invariant.withEarlyReturn
      -- 早期リターンしたとき
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      -- 通常の帰納ステップ
      (onContinue := fun xs seen => ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  all_goals mleave; grind

/-
最初の `mySum` 例と同様に、この証明も簡潔な構造を保っています。というのも、今回も `grind` と、`List.Nodup` をめぐる既存の枠組みに証明の大半を委ねているからです。
したがって、違いは不変条件にあるだけです。
ループに早期 `return` があるため、補助関数 `Invariant.withEarlyReturn` を使って不変条件を構成します。
この関数によって、不変条件を次の三つの部分に分けて指定できます。

* `onReturn ret seen` は、ループが値 `ret` を伴う早期 `return` によって抜けた後に成り立つべき性質です。
  `nodup` の場合、返される唯一の値は `false` であり、そのとき `nodup` はリストに重複があると判定したことになります。

* `onContinue xs seen` は、各反復で不変条件が保存されることを示す通常の帰納ステップです。
  反復の状態はカーソル `xs` によって表現されます。
  与えられた例では、集合 `seen` がこれまでのループ反復で現れたすべての要素を含み、かつこれまで重複がなかったことを主張します。


`onExcept` は、ループが例外を投げたときに成り立つべき性質です。
`Id` には例外がないため、ここは指定せずデフォルトを用います。
（例外については後で議論します。）

では、`mvcgen` を使わない直接的（かつ過度にゴルフされた）証明を次に示します：
-/

theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]

/-
いくつか所見が得られます：

* この証明は、`mvcgen` を用いたものよりさらに短い。
* `generalize` を使ってアキュムレータを一般化する方法は、一般化の対象となる `∅` の出現箇所がちょうど1つであることに依存している。
  もしそうでなければ、証明の中にプログラムの一部を持ち込まざるを得ず、これは大きな関数に対しては現実的ではない。
* 適切な補題が与えられていれば、`grind` は関数の制御フローに沿って分割し、`Id` について推論してくれる。
  これは `Id.run_pure` や `Id.run_bind` には効くが、たとえば `Id.run_seq` には効かない。
  というのも、その補題は E-matchable ではないからだ。
  `grind` が失敗する場合は、`grind` が再び拾えるところまで、制御フローの分割やモナディックな推論をすべて手作業で行わざるを得ない。

証明対象の定義の制御フローを複製せずに済ませる通常の方法は、`fun_cases` や `fun_induction` タクティクを用いることです。
しかし残念ながら、例えば `forIn` の適用内部にある制御フローについては、`fun_cases` は助けになりません。

これは mvcgen と対照的です。mvcgen には多くの `forIn` 実装のサポートが同梱されており、カスタムの `forIn` 実装についても `@[spec]` アノテーションを付けるだけで容易に拡張できます。
さらに、mvcgen による証明では、元のプログラムの一部をコピーしなければならない状況は決して発生しません。
-/

/-
## Hoare 三つ組を用いた副作用を持つプログラムに対する合成的推論

これまでの例では、`Id.run do <prog>` を使って定義された関数について推論し、`<prog>` 内でのローカルな可変性や早期リターンを利用してきた。
しかし、実際のプログラムでは、状態や失敗条件を暗黙の「効果」として隠蔽するために、しばしば `do` 記法とモナド `M` が使われる。
この場合、関数は通常 `M.run` を省略し、代わりにモナディックな戻り値型 `M α` を持ち、その型を持つ他の関数とよく合成できるようになっている。

以下は、自動インクリメントのカウンタ値を返す状態付き関数 `mkFresh` を用いた例です。
-/

structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify (fun s => {s with counter := s.counter + 1})
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

/-
`mkFreshN n` は、`mkFresh` を通じて内部の Supply 状態を変更しながら、n 個の「新しい」数を返します。
ここで「新しい」とは、これまでに生成された数のすべてが、次に生成される数と異なることを意味します。
この正しさの性質を、`List.Nodup` を用いて `mkFreshN_correct` として定式化し、証明することができます。
-/

theorem mkFreshN_correct {s : Supply} (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- `(mkFreshN n).run' s` に注目する
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- モナディックなプログラム `mkFresh n` について述べる
  -- `mvcgen` への `mkFreshN` と `mkFresh` の引数は内部の `simp` 集合に追加され、
  -- `mvcgen` がこれらの定義を展開するようにする
  mvcgen [mkFreshN, mkFresh]
  -- 不変条件：カウンタは蓄積済みのあらゆる数より大きく、
  --         かつ蓄積済みの数はすべて相異なる
  -- この不変条件は引数 `state : Supply` を通じて状態を参照することができる
  -- 次に蓄積する数はカウンタであるため、蓄積済みのすべての数と異なる
  case inv1 => exact ⇓⟨xs, acc⟩ state => ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

/- ### 仕様の合成

`mvcgen [mkFreshN, mkFresh]` のように定義を入れ子にして展開する方法は、かなり大ざっぱですが、小さなプログラムに対しては有効です。
より合成的な方法としては、各モナディック関数ごとに個別の仕様補題を作成することです。
これらの補題は、`mvcgen` への引数として渡すこともできますし、`@[spec]` 補題を用いて、仕様のグローバル（あるいはスコープ付き、ローカル）データベースに登録することもできます。
-/

/-- mkFresh は

1. 今のカウンタ値を返す
2. カウンタをインクリメントする
-/
@[spec]
theorem mkFresh_spec (c : Nat) : ⦃fun state => ⌜state.counter = c⌝⦄ mkFresh ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- `mkFresh` を展開して一気に片を付ける
  mvcgen [mkFresh]
  grind

@[spec]
theorem mkFreshN_spec (n : Nat) : ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `mkFresh_spec` が `@[spec]` で登録されていなければ `mvcgen [mkFreshN, mkFresh_spec]` とする
  mvcgen [mkFreshN]
  -- 先と同様
  case inv1 => exact ⇓⟨xs, acc⟩ state => ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  all_goals mleave; grind

theorem mkFreshN_correct₂ {s : Supply} (n : Nat) : ((mkFreshN n).run' s).Nodup :=
  -- `mkFreshN` の型 `⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄` は
  -- `∀ (n : Nat) (s : Supply), True → ((mkFreshN n).run' s).Nodup` と定義的等価
  mkFreshN_spec n s True.intro

/-
ここでの記法 `⦃fun state => ⌜state.counter = c⌝⦄ mkFresh ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄` は、Hoare 三つ組（cf. Std.Do.Triple）を表している。
モナディック関数の仕様は、常にこのような Hoare 三つ組の結果型を持つ。
-/

/- ### Hoare 三つ組

ホーア三つ組 `⦃P⦄ prog ⦃Q⦄` は、「状態に対して前提条件 P が成り立つならば、モナディックプログラム prog を実行した後には後提条件 Q が成り立つ」という意味です。
したがって、`mkFresh` の仕様定理は次のように述べられます：

> もし `c` が `Supply` の事前状態（prestate）のカウンタフィールドを表しているなら、`mkFresh` を実行すると戻り値として `c` を返し、事後状態（poststate）のカウンタを `c` より大きい値に更新します。

この仕様は「情報を捨てている（lossy）」ことに注意してください。
`mkFresh` は状態を任意の非負の量だけ増加させても、依然としてこの仕様を満たします。
これは望ましい性質です。なぜなら、仕様は興味のない実装の詳細を抽象化できるため、堅牢で小さな証明を保つことができるからです。

ホーア三つ組は、状態付き述語の論理と、モナディックプログラムをその論理に翻訳する「最弱事前条件」意味論 `wp⟦·⟧` に基づいて定義されます。

```lean
def Triple [WP m ps] {α : Type u} (x : m α) (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦x⟧ Q
```
-/
--#--
/--
info: def Std.Do.Triple.{u, v} : {m : Type u → Type v} →
  {ps : PostShape} → [WP m ps] → {α : Type u} → m α → Assertion ps → PostCond α ps → Prop :=
fun {m} {ps} [WP m ps] {α} x P Q => P ⊢ₛ wp⟦x⟧ Q
-/
#guard_msgs in
#print Triple
--#--
/-
`WP` 型クラスはモナド `m` をその `ps : PostShape` に対応付けます。この `PostShape` が、ホーア三つ組の具体的な形を決定します。
`StateT`、`ReaderT`、`ExceptT` などの標準的なモナド変換子の多くには、標準的な（canonical）`WP` インスタンスが付属しています。

たとえば、`StateT σ` には、すべての主張（Assertion）に対して `σ` 引数を追加する `WP` インスタンスがあります。
状態付き含意 `⊢ₛ` は、これらの追加された `σ` 引数に対して η 展開されます。

`StateM` プログラムに関しては、次の型がホーア三つ組 `Triple` と定義的等価になります。
-/

def Triple' {α σ : Type u} (x : StateM σ α) (P : σ → ULift Prop) (Q : (α → σ → ULift Prop) × PUnit) : Prop :=
  ∀ s, (P s).down → let (a, s') := x.run s; (Q.1 a s').down

example : @Triple' α σ = Triple (m := StateM σ) := rfl

/-
一般的な後提条件記法 `⇓ r => ...` は、型 `α → Assertion ps` の主張を `PostCond ps` へと埋め込みます。
`StateM` の場合は、これを空のタプル `PUnit.unit` と結合して実現します。

例外が加わると、後提条件の形はさらに興味深いものになります。

記法 `⌜p⌝` は、純粋な仮定 `p : Prop` を状態付き主張（stateful assertion）へと埋め込みます。
逆に、任意の状態付き仮定 `h : Assertion ps` が、ある `p : Prop` に対して `⌜p⌝` と同値であるとき、それを「純粋（pure）」と呼びます。

純粋な状態付き仮定は、通常の Lean のコンテキストと自由に行き来させることができます。
（これを手動で行うには、`mpure` タクティックを使います。）

#### 純粋な前提条件とフレーム規則の概念に関する進んだ補足

この小節は少し脇道にそれる内容なので、初読では飛ばしてかまいません。

Aeneas に着想を得たモナディックな加算関数 `x +? y : M UInt8` の仕様が「加算がオーバーフローしない」、すなわち `h : x.toNat + y.toNat ≤ UInt8.size` を要件として課すとします。
この要件は、仕様の通常の Lean の仮定（`add_spec_hyp`）としてエンコードすべきでしょうか？ それとも、`⌜·⌝` 記法を用いて、ホーア三つ組の純粋な前提条件（`add_spec_pre`）としてエンコードすべきでしょうか？

```lean
theorem add_spec_hyp (x y : UInt8) (h : x.toNat + y.toNat ≤ UInt8.size) :
    ⦃⌜True⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := sorry

theorem add_spec_pre (x y : UInt8) :
    ⦃⌜x.toNat + y.toNat ≤ UInt8.size⌝⦄ x +? y ⦃⇓ r => ⌜r.toNat = x.toNat + y.toNat⌝⦄ := sorry
```

第一のアプローチを勧めます。もっとも、実際上は差が出ないはずです。
VC 生成器（Verification Condition generator）は、純粋な仮定を状態付きコンテキストから通常の Lean のコンテキストへ移動させるため、第二の形式は事実上、第一の形式へと変換されます。
これは「仮定のフレーミング（framing hypotheses）」と呼ばれます（`mpure` および `mframe` タクティック参照）。

Lean のコンテキスト内にある仮定は、状態付き論理における不変のフレーム（immutable frame）の一部です。というのも、状態付き仮定と異なり、これらは帰結規則（rule of consequence）を適用しても保持されるからです。
-/
