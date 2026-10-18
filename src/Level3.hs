-- | Домашка 3. Специальный (ad-hoc) полиморфизм: уровень 3.

-- Семейства типов в 3.1 вызывают друг друга во вложенных аппликациях; GHC требует для этого
-- явно разрешить определения, завершимость которых он проверить не может.
{-# LANGUAGE UndecidableInstances #-}
module Level3 where

import Defs
import GHC.TypeLits (Symbol)


-- 3.1. Формулы вычисляются в типах
--
-- Реализуйте семейство типов Eval: значение формулы Prop над переменными-строками
-- в окружении env — списке пар (имя, значение) уровня типов.
--
--   Eval '[ '("a", True), '("b", False) ] (Var "a" :-> Var "b")  ~  False
--
-- Скорее всего, понадобятся вспомогательные семейства: поиск переменной в окружении
-- и логические операции над Bool уровня типов. Проверять себя удобно в интерпретаторе
-- командой :kind!.
--
-- Тесты подставляют полные окружения (все переменные формулы определены); на них семейство
-- обязано вычисляться до True или False, иначе тесты не соберутся.

type family Lookup (env :: [(Symbol, Bool)]) (s :: Symbol) :: Bool where
  Lookup ('(s, v) : env) s = v
  Lookup (_ : env) s = Lookup env s

type family ENot (op :: Bool) where
  ENot False = True
  ENot True = False

type family EAnd (l :: Bool) (r :: Bool) where
  EAnd False _ = False
  EAnd _ False = False
  EAnd True True = True

type family EOr (l :: Bool) (r :: Bool) where
  EOr True _ = True
  EOr _ True = True
  EOr False False = False

type family EImp (l :: Bool) (r :: Bool) where
  EImp False _ = True
  EImp True False = False
  EImp True True = True

type family Eval (env :: [(Symbol, Bool)]) (p :: Prop Symbol) :: Bool where
  Eval env (Var s) = Lookup env s
  Eval env (Not p) = ENot (Eval env p)
  Eval env (l :\/ r) = EOr (Eval env l) (Eval env r)
  Eval env (l :/\ r) = EAnd (Eval env l) (Eval env r)
  Eval env (l :-> r) = EImp (Eval env l) (Eval env r)
