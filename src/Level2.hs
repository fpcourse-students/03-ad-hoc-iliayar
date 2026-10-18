-- | Домашка 3. Специальный (ad-hoc) полиморфизм: уровень 2.

-- Ограничение All ((<--) m) as в 2.2 вычисляется семейством типов.
{-# LANGUAGE UndecidableInstances #-}
module Level2 where

import Control.Monad.State (State, runState, MonadState (get, put), modify)
import Data.Dynamic (Dynamic, fromDynamic, toDyn)
import Data.Hashable (Hashable (hash, hashWithSalt))
import Data.Kind (Type)
import Data.List qualified as List
import Data.Map qualified as Map
import Data.Typeable (Typeable)
import Defs
import MetaUtils (todo)
import Data.Monoid (Sum (Sum, getSum))


-- 2.1. Свёртка гетерогенного списка
--
-- HSum tys — значение ровно одного из типов списка tys: Here x — первого, There s —
-- какого-то из остальных. Это сумма типов, как HList — их произведение.
--
-- hfoldMap сворачивает гетерогенный список в моноид. Обработчик у неё один на все элементы:
-- он получает элемент вместе с его позицией в списке, то есть значение HSum tys.
-- Результаты соединяются слева направо; от пустого списка — mempty.
--
-- sumParticular складывает числа списка; Nothing считается нулём. В обработчике GHC
-- попросит ветку и для There (There s), хотя значений такого вида не бывает: у s тип
-- HSum '[]. Убедить компилятор, что варианты перебраны, можно пустым case: case s of {}.

data HSum (tys :: [Type]) where
  Here :: ty -> HSum (ty ': tys)
  There :: HSum tys -> HSum (ty ': tys)

hfoldMap :: (Monoid m, HFoldMap tys) => (HSum tys -> m) -> HList tys -> m
hfoldMap = hfoldMapImpl

class HFoldMap (tys :: [Type]) where
  hfoldMapImpl :: (Monoid m) => (HSum tys -> m) -> HList tys -> m

instance HFoldMap '[] where
  hfoldMapImpl _ _ = mempty

instance (HFoldMap tys) => HFoldMap (ty : tys) where
  hfoldMapImpl f (HCons x xs) =
    f (Here x) <> hfoldMap (\hsum -> f $ There hsum) xs

sumParticular :: HList '[Maybe Int, Int] -> Int
sumParticular =
  getSum
    . hfoldMap
      ( \case
          Here (Just x) -> Sum $ x
          Here Nothing -> Sum 0
          There (Here x) -> Sum x
          There (There hsum) -> case hsum of {}
      )


-- 2.2. Обработчики выбирает компилятор
--
-- Передать одну функцию от суммы — всё равно что передать по функции на каждый тип списка.
-- Пусть этот набор функций строит компилятор. Класс to <-- from — функция transform
-- из from в to, выбранная по обоим типам. Ограничение All ((<--) m) tys требует такую
-- функцию в m для каждого типа списка.
--
-- Реализуйте hfoldMap' и sumParticular' (то же, что sumParticular) и объявите инстансы
-- класса, которые для этого нужны.

class to <-- from where
  transform :: from -> to

hfoldMap' :: forall m tys . (Monoid m, All ((<--) m) tys) => HList tys -> m
hfoldMap' hlst = mconcat $ hmap @((<--) m) transform hlst

instance Sum Int <-- Maybe Int where
    transform Nothing = Sum 0
    transform (Just x) = Sum x

instance Sum Int <-- Int where
    transform = Sum

sumParticular' :: HList '[Maybe Int, Int] -> Int
sumParticular' = getSum . hfoldMap'


-- 2.3. Кеширующий декоратор
--
-- cached превращает функцию от произвольного числа аргументов (они собраны в HList)
-- в функцию, которая запоминает результаты. Кеш один на все функции и все типы
-- результатов, поэтому значения лежат в нём динамически типизированными (Data.Dynamic),
-- а ключом служит хеш списка аргументов. Совпадения хешей у разных аргументов не разбираем.
--
--   * newKey строит ключ по хешируемому значению; тип результата в ключе — фантомный;
--   * runCached запускает вычисление с пустым кешем и возвращает результат вместе
--     с итоговым кешем, evalCached — только результат;
--   * getCache возвращает значение по ключу; Nothing — если ключа нет или под ним лежит
--     значение другого типа;
--   * storeCache кладёт значение по ключу;
--   * cached f args: если результат для args в кеше есть, он возвращается, а f не
--     вызывается; иначе результат вычисляется, кладётся в кеш и возвращается.
--
-- Тесты смотрят и на итоговый кеш: в нём ровно по одной записи на каждый набор аргументов,
-- ключ записи — hash списка аргументов.

-- | Типизированный ключ динамического гетерогенного хранилища.
newtype Key ty = Key { getKeyHash :: Int }
  deriving newtype (Eq, Ord)

-- | Вычисление с изменяемым кешем.
type Cached a = State (Map.Map Int Dynamic) a

newKey :: Hashable a => a -> Key b
newKey = Key . hash

runCached :: Cached a -> (a, Map.Map Int Dynamic)
runCached cached = runState cached Map.empty

evalCached :: Cached a -> a
evalCached cached = fst $ runCached cached

getCache :: (Typeable ty) => Key ty -> Cached (Maybe ty)
getCache key = do
  m <- get
  case Map.lookup (getKeyHash key) m of
    Nothing -> return Nothing
    Just v -> return $ fromDynamic v

storeCache :: Typeable ty => Key ty -> ty -> Cached ()
storeCache key v = do
    modify $ Map.insert (getKeyHash key) $ toDyn v

cached
  :: (All Eq tys, All Hashable tys, Typeable res)
  => (HList tys -> res) -> HList tys -> Cached res
cached f args = do
    let key = newKey args
    cached <- getCache key
    case cached of
        Just res -> return res
        Nothing -> do
            let res = f args
            storeCache key res
            return res

-- Пример для экспериментов: сумма первых n чисел Фибоначчи считается долго, а повторный
-- вызов с теми же аргументами берёт ответ из кеша. Время видно в интерпретаторе после
-- команды :set +s.

fibs :: [Integer]
fibs = 1 : 1 : zipWith (+) fibs (drop 1 fibs)

sumNFibs :: HList '[Integer] -> Integer
sumNFibs (HCons n HNil) = sum $ List.genericTake n fibs

testCached :: Integer -> Integer -> Integer
testCached n m = evalCached do
  let f = cached sumNFibs
  x <- f (HCons n HNil)
  y <- f (HCons m HNil)
  pure (x + y)
