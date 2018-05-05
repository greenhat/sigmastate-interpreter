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

  property("rule110 scala") {
    case class Transaction(inputs: Seq[InputOutput], outputs: Seq[InputOutput]) {
      def isCorrect: Boolean = inputs.forall(input => input.script(input, this))
    }
    case class InputOutput(script: (InputOutput, Transaction) => Boolean, register: Seq[Byte])
    val layerLength = 31

    val rule110Script: (InputOutput, Transaction) => Boolean = { (input: InputOutput, tx: Transaction) =>
      val oldLayer = input.register
      val newLayer = tx.outputs.head.register
      (0 until layerLength).forall { i =>
        val output = newLayer(i)
        val input0 = if (i == 0) oldLayer.last else oldLayer(i - 1)
        val input1 = oldLayer(i)
        val input2 = if (i == layerLength - 1) oldLayer.head else oldLayer(i + 1)
        val oneBitRule110 = {
          ((input0 == 1) && (input1 == 1) && (input2 == 1) && (output == 0)) ||
            ((input0 == 1) && (input1 == 1) && (input2 == 0) && (output == 1)) ||
            ((input0 == 1) && (input1 == 0) && (input2 == 1) && (output == 1)) ||
            ((input0 == 1) && (input1 == 0) && (input2 == 0) && (output == 0)) ||
            ((input0 == 0) && (input1 == 1) && (input2 == 1) && (output == 1)) ||
            ((input0 == 0) && (input1 == 1) && (input2 == 0) && (output == 1)) ||
            ((input0 == 0) && (input1 == 0) && (input2 == 1) && (output == 1)) ||
            ((input0 == 0) && (input1 == 0) && (input2 == 0) && (output == 0))
        }
        val outputSctiptIsTheSame = tx.outputs.head.script == input.script
        oneBitRule110 && outputSctiptIsTheSame
      }
    }

    val layers = Seq(
      Seq(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
      Seq(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
      Seq(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
      Seq(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
      Seq(0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0),
      Seq(0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    ).map(_.map(_.toByte))

    (0 until layers.length - 1).foreach { i =>
      val tx = Transaction(
        Seq(InputOutput(rule110Script, layers(i))),
        Seq(InputOutput(rule110Script, layers(i + 1)))
      )
      require(tx.isCorrect)
    }
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