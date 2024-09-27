theory RecursiveTreeFunctions
imports Main
begin

datatype 'a arvbin = Vazia | Nodo "'a arvbin" 'a "'a arvbin"

fun tamanho :: "'a list \<Rightarrow> nat" where
  "tamanho [] = 0" |
  "tamanho (h # T) = Suc (tamanho T)"

fun numnodos :: "'a arvbin \<Rightarrow> nat" where
  "numnodos Vazia = 0" |
  "numnodos (Nodo L x R) = 1 + numnodos L + numnodos R"

fun espelho :: "'a arvbin \<Rightarrow> 'a arvbin" where
  "espelho Vazia = Vazia" |
  "espelho (Nodo L x R) = Nodo (espelho R) x (espelho L)"

fun conteudo :: "'a arvbin \<Rightarrow> 'a list" where
  "conteudo Vazia = []" |
  "conteudo (Nodo L x R) = conteudo L @ [x] @ conteudo R"

(* Prova da propriedade: numnodos(A) = tamanho(conteudo(A)) *)
lemma numnodos_conteudo: "numnodos A = tamanho (conteudo A)"
proof (induct A)
  case Vazia
  (* Caso base: A é uma árvore vazia *)
  show "numnodos Vazia = tamanho (conteudo Vazia)"
  proof -
    have "numnodos Vazia = 0" by simp
    moreover have "conteudo Vazia = []" by simp
    moreover have "tamanho [] = 0" by simp
    finally show numnodos Vazia = tamanho (conteudo Vazia) by simp
  qed
next
  case (Nodo L x R)
  (* Passo indutivo: A = Nodo L x R *)
  assume IH_L: "numnodos L = tamanho (conteudo L)"
  assume IH_R: "numnodos R = tamanho (conteudo R)"
  (* Queremos mostrar que: numnodos (Nodo L x R) = tamanho (conteudo (Nodo L x R)) *)
  show "numnodos (Nodo L x R) = tamanho (conteudo (Nodo L x R))"
proof -
  have "numnodos (Nodo L x R) = Suc (numnodos L + numnodos R)" by simp
  moreover have "... = Suc (tamanho (conteudo L) + numnodos R)" by (simp only: IH_L)
  moreover have "... = Suc (tamanho (conteudo L) + tamanho (conteudo R))" by (simp only: IH_R)
  moreover have "... = Suc (tamanho (conteudo L @ conteudo R))" by simp
  moreover have "... = tamanho (x # (conteudo L @ conteudo R))" by simp
  moreover have "... = tamanho (conteudo (Nodo L x R))" by simp
  finally show "numnodos (Nodo L x R) = tamanho (conteudo (Nodo L x R))" by simp
  qed
qed


end