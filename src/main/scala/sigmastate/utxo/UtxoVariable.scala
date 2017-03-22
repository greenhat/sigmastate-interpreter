package sigmastate.utxo

import sigmastate._
import org.bitbucket.inkytonik.kiama.rewriting.Rewriter.{everywherebu, everywheretd, rule}

import scala.collection.mutable


case class UtxoContext(currentHeight: Int,
                       spendingTransaction: SigmaStateTransaction,
                       self: SigmaStateBox)

trait UtxoVariable[V <: Value] extends Variable[V]

case object OutputAmount extends Variable[IntLeaf]

//information needed

//todo: more strict-type solution Variable[V] => Value[V]
case class ScopedBinding(bindings: Map[Variable[_], Value], relations: Seq[Relation]) extends StateTree

trait Function extends StateTree

case class TxHasOutput(relation: Relation*) extends Function

object UtxoSubstitution {

  def fnSubst(utxoContext: UtxoContext) = rule[SigmaStateTree] {
    case hasOut: TxHasOutput =>
      val ts = hasOut.relation.map { r =>
        (r.left, r.right) match {
          case (OutputAmount, _) | (_, OutputAmount) => OutputAmount -> r
          case _ => ???
        }
      }

      val sbs = utxoContext.spendingTransaction.newBoxes.map { out =>
        val amount = out.value
        val bs = mutable.Map[Variable[_], Value]()

        val rs = ts.map { case (v, r) =>
          v match {
            case OutputAmount =>
              bs.put(OutputAmount, IntLeaf(amount))
              r
            case _ => ???
          }
        }
        ScopedBinding(bs.toMap, rs)
      }

      OR(sbs.toSeq)
  }

  def sbSubst = rule[SigmaStateTree] {
    case sb: ScopedBinding =>
      val rels = sb.relations.map { r =>
        val rl = r.left match {
          case v: Variable[_] =>
            sb.bindings.get(v) match {
              case Some(value) => r.swapLeft(value)
              case None => r
            }
          case _ => r
        }

        rl.right match {
          case v: Variable[_] =>
            sb.bindings.get(v) match {
              case Some(value) => rl.swapRight(value)
              case None => rl
            }
          case _ => rl
        }
      }
      AND(rels)
  }
}

