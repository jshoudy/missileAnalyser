[Call Graph] For information on where the call graph may be incomplete, use the verbose option to the cg phase.
[Spark] Pointer Assignment Graph in 0.3 seconds.
[Spark] Type masks in 0.0 seconds.
[Spark] Pointer Graph simplified in 0.0 seconds.
[Spark] Propagation in 0.0 seconds.
[Spark] Solution found in 0.0 seconds.
successfully constructed ExampleTest
called run
  flowThrough called with r0 := @this: ExampleTest, in: <Top>
    handleDef called with ThisRef: r0 = @this: ExampleTest
      We are in a method in class ExampleTest
  fallOut = [<Top>]
  branchOuts = []
  flowThrough called with specialinvoke r0.<java.lang.Object: void <init>()>(), in: <Top>
    Entering handleInvoke specialinvoke r0.<java.lang.Object: void <init>()>()
    Constructor call on ExampleTest!
    Adding arguments (count: 0) to this.constructorCalls with key: r0
    fallOut = [<Top>]
    branchOuts = []
    flowThrough called with return, in: <Top>
    fallOut = [<Bottom>]
    branchOuts = [<Bottom>]
successfully constructed ExampleTest
called run
  flowThrough called with $r0 = new MissileBattery, in: <Top>
    handleDef called with JNewExpr: $r0 = new MissileBattery
      Entering NewExpr
      SKIPING: Assigning newObject of type new MissileBattery to $r0
  fallOut = [<Top>]
  branchOuts = []
  flowThrough called with specialinvoke $r0.<MissileBattery: void <init>(int)>(6), in: <Top>
    Entering handleInvoke specialinvoke $r0.<MissileBattery: void <init>(int)>(6)
    Constructor call on MissileBattery!
      * Got argument: 6
    Adding arguments (count: 1) to this.constructorCalls with key: $r0
    fallOut = [<Top>]
    branchOuts = []
    flowThrough called with r1 = $r0, in: <Top>
      handleDef called with JimpleLocal: r1 = $r0
        Entering JimpleLocal
        env.hasVar($r0) is false
        constructorCalls contains '$r0'.
        adding {r1,$r0} to missileBatteryAssignments
    fallOut = [<Top>]
    branchOuts = []
    flowThrough called with z0 = 0, in: <Top>
      handleDef called with IntConstant: z0 = 0
            Assigning IntConstant of value 0
    fallOut = [{  1z0 = 0 }]
    branchOuts = []
    flowThrough called with z1 = 0, in: {  1z0 = 0 }
      handleDef called with IntConstant: z1 = 0
            Assigning IntConstant of value 0
    fallOut = [{  1z1 = 0;  1z0 = 0 }]
    branchOuts = []
    flowThrough called with if z0 != 0 goto b0 = 6, in: {  1z1 = 0;  1z0 = 0 }
    condition: z0 != 0
      called handleIf with expr: z0 != 0
      eq expr with local int
      false: {  1z1 = 0;  1z0 = 0 } meet  1z0 = 0 join null
      true:{  1z1 = 0;  1z0 = 0 } meet  1z0 > 0 join  -1z0 > 0
      result false: {  1z1 = 0;  1z0 = 0 }
      result true: <Bottom>
    fallOut = [{  1z1 = 0;  1z0 = 0 }]
    branchOuts = [<Bottom>]
    flowThrough called with b0 = 6, in: <Bottom>
      handleDef called with IntConstant: b0 = 6
            Assigning IntConstant of value 6
    fallOut = [<Bottom>]
    branchOuts = []
    flowThrough called with b0 = 5, in: {  1z1 = 0;  1z0 = 0 }
      handleDef called with IntConstant: b0 = 5
            Assigning IntConstant of value 5
    fallOut = [{  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }]
    branchOuts = []
    flowThrough called with goto [?= virtualinvoke r1.<MissileBattery: void fire(int)>(b0)], in: {  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }
      flowThrough called with virtualinvoke r1.<MissileBattery: void fire(int)>(b0), in: {  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }
        Entering handleInvoke virtualinvoke r1.<MissileBattery: void fire(int)>(b0)
          Entering MissileBattery.fire(int)
          missileIdxInterval = [5,5]
          Checking that [5,5] is a subset of [0,5]
          OK:)
          Checking that [5,5] has not been already fired
      fallOut = []
      branchOuts = [{  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }]
    fallOut = []
    branchOuts = [{  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }]
    merge from unit virtualinvoke r1.<MissileBattery: void fire(int)>(b0)
      merge: {  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 } + <Bottom> = {  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }
      flowThrough called with virtualinvoke r1.<MissileBattery: void fire(int)>(b0), in: {  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }
        Entering handleInvoke virtualinvoke r1.<MissileBattery: void fire(int)>(b0)
          Entering MissileBattery.fire(int)
          missileIdxInterval = [5,5]
          Checking that [5,5] is a subset of [0,5]
          OK:)
          Checking that [5,5] has not been already fired
          ** UNSAFE!! [5,5] (missile index) overlaps with already fired interval [5,5]
      fallOut = [{  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }]
      branchOuts = []
      flowThrough called with return, in: {  1z1 = 0;  1z0 = 0;  1b0 -5 = 0 }
      fallOut = [<Bottom>]
      branchOuts = [<Bottom>]
Program ExampleTest is UNSAFE
