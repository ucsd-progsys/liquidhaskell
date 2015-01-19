module AmortizedQueue where

import Prelude hiding (head)

data AbsQueue a = AQ { front :: [a]
                     , rear  :: [a] }

{-@ data AbsQueue a = AQ { front :: [a]
                         , rear  :: {v:[a] | size v <= size front} }  @-}

{-@ die :: {v:String | false} -> a @-}
die :: String -> a
die x = error x

{-@ measure size @-}
size        :: [a] -> Int
size []     = 0
size (x:xs) = 1 + size xs

{-@ measure qsize @-}
qsize            :: AbsQueue a -> Int
qsize (AQ xs ys) = size xs + size ys

{-@ invariant {v:[a]        | size v >=  0} @-}
{-@ invariant {v:AbsQueue a | qsize v >= 0} @-}

{-@ type NEList  a = {v:[a]        | size v > 0} @-}
{-@ type NEQueue a = {v:AbsQueue a | qsize v > 0} @-}


makeQueue            :: [a] -> [a] -> AbsQueue a
makeQueue f b
  | size b <= size f = AQ f b
  | otherwise        = AQ (f ++ reverse b) []

                       
{- measure qhead @-}

{-@ qhead      :: NEQueue a -> a @-}
qhead (AQ f _) = head f
qhead _        = die "never"

{- measure head @-}

{-@ head   :: NEList a -> a @-}
head (x:_) = x
-- head _     = die "never"


{- toList :: q:AbsQueue a -> {v:[a] | 0 < len v => head v = front q} @-}
toList :: AbsQueue a -> [a]
toList = undefined 
-- forall q :: AbsQueue a, xs:: [a], x::a.
--    not (isEmpty(q)) && asList(q) == xs =>                    
{-
import leon.lang._
import leon.annotation._

object AmortizedQueue {
  sealed abstract class List
  case class Cons(head : Int, tail : List) extends List
  case object Nil extends List

  sealed abstract class AbsQueue
  case class Queue(front : List, rear : List) extends AbsQueue

  def size(list : List) : Int = (list match {
    case Nil => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  def content(l: List) : Set[Int] = l match {
    case Nil => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ content(xs)
  }
  
  def asList(queue : AbsQueue) : List = queue match {
    case Queue(front, rear) => concat(front, reverse(rear))
  }

  def concat(l1 : List, l2 : List) : List = (l1 match {
    case Nil => l2
    case Cons(x,xs) => Cons(x, concat(xs, l2))
  }) ensuring (res => size(res) == size(l1) + size(l2) && content(res) == content(l1) ++ content(l2))

  def isAmortized(queue : AbsQueue) : Boolean = queue match {
    case Queue(front, rear) => size(front) >= size(rear)
  }

  def isEmpty(queue : AbsQueue) : Boolean = queue match {
    case Queue(Nil, Nil) => true
    case _ => false
  }

  def reverse(l : List) : List = (l match {
    case Nil => Nil
    case Cons(x, xs) => concat(reverse(xs), Cons(x, Nil))
  }) ensuring (content(_) == content(l))

  def amortizedQueue(front : List, rear : List) : AbsQueue = {
    if (size(rear) <= size(front))
      Queue(front, rear)
    else
      Queue(concat(front, reverse(rear)), Nil)
  } ensuring(isAmortized(_))

  def enqueue(queue : AbsQueue, elem : Int) : AbsQueue = (queue match {
    case Queue(front, rear) => amortizedQueue(front, Cons(elem, rear))
  }) ensuring(isAmortized(_))

  def tail(queue : AbsQueue) : AbsQueue = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, fs), rear) => amortizedQueue(fs, rear)
    }
  } ensuring (isAmortized(_))

  def front(queue : AbsQueue) : Int = {
    require(isAmortized(queue) && !isEmpty(queue))
    queue match {
      case Queue(Cons(f, _), _) => f
    }
  }

  @induct
  def propFront(queue : AbsQueue, list : List) : Boolean = {
    require(!isEmpty(queue) && isAmortized(queue))
    if (asList(queue) == list) {
      list match {
        case Cons(x, _) => front(queue) == x
      }
    } else
      true
  } holds

  def enqueueAndFront(queue : AbsQueue, elem : Int) : Boolean = {
    if (isEmpty(queue))
      front(enqueue(queue, elem)) == elem
    else
      true
  } holds

  def enqueueDequeueThrice(queue : AbsQueue, e1 : Int, e2 : Int, e3 : Int) : Boolean = {
    if (isEmpty(queue)) {
      val q1 = enqueue(queue, e1)
      val q2 = enqueue(q1, e2)
      val q3 = enqueue(q2, e3)
      val e1prime = front(q3)
      val q4 = tail(q3)
      val e2prime = front(q4)
      val q5 = tail(q4)
      val e3prime = front(q5)
      e1 == e1prime && e2 == e2prime && e3 == e3prime
    } else
      true
  } holds
}

-}
