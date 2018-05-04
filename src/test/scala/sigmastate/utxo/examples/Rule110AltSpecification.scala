package sigmastate.utxo.examples

import org.scalatest.prop.{GeneratorDrivenPropertyChecks, PropertyChecks}
import org.scalatest.{Matchers, PropSpec}
import sigmastate.Values._
import sigmastate._
import sigmastate.helpers.ErgoProvingInterpreter
import sigmastate.utxo.ErgoBox.R4
import sigmastate.utxo._

/**
  * Wolfram's Rule110 alternative implementation
  *
  * A coin holds following data:
  *
  * R4 - current layer
  */
class Rule110AltSpecification extends PropSpec
  with PropertyChecks
  with GeneratorDrivenPropertyChecks
  with Matchers {

  def calcRule110(left: Boolean, center: Boolean, right: Boolean): Boolean =
    (left, center, right) match {
      case (true, true, true) => false
      case (true, true, false) => true
      case (true, false, true) => true
      case (true, false, false) => false
      case (false, true, true) => true
      case (false, true, false) => true
      case (false, false, true) => true
      case (false, false, false) => false
    }

  property("rule110") {
    val prover = new ErgoProvingInterpreter()

    val bitsInString = 31
    val t = IntConstant(1)
    val f = IntConstant(0)

    val indexCollection = new ConcreteCollection((0 until bitsInString).map(i => IntConstant(i)))
    val oldLayer = ExtractRegisterAs[SByteArray.type](ByIndex(Inputs, 0), R4)
    val newLayer = ExtractRegisterAs[SByteArray.type](ByIndex(Outputs, 0), R4)

    val index = TaggedInt(21)
    val output = GetByteByIndex(newLayer, index)
    val firstElement = GetByteByIndex(oldLayer, 0)
    val lastElement = GetByteByIndex(oldLayer, bitsInString)
    val input0 = GetByteByIndex(oldLayer, Minus(index, 1), Some(lastElement))
    val input1 = GetByteByIndex(oldLayer, index)
    val input2 = GetByteByIndex(oldLayer, Plus(index, 1), Some(firstElement))


    val oneBitRule110 = OR(Seq(
      AND(EQ(input0, t), EQ(input1, t), EQ(input2, t), EQ(output, f)),
      AND(EQ(input0, t), EQ(input1, t), EQ(input2, f), EQ(output, t)),
      AND(EQ(input0, t), EQ(input1, f), EQ(input2, t), EQ(output, t)),
      AND(EQ(input0, t), EQ(input1, f), EQ(input2, f), EQ(output, f)),
      AND(EQ(input0, f), EQ(input1, t), EQ(input2, t), EQ(output, t)),
      AND(EQ(input0, f), EQ(input1, t), EQ(input2, f), EQ(output, t)),
      AND(EQ(input0, f), EQ(input1, f), EQ(input2, t), EQ(output, t)),
      AND(EQ(input0, f), EQ(input1, f), EQ(input2, f), EQ(output, f))
    ))

    val rule110 = ForAll(indexCollection, 21, oneBitRule110)

    val unchangedScript = EQ(ExtractScriptBytes(Self), ExtractScriptBytes(ByIndex(Outputs, 0)))
    val proposition = AND(unchangedScript, rule110)



  }
}