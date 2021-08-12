﻿using System;
using System.Diagnostics.CodeAnalysis;

namespace LogicCircuit {
	[SuppressMessage("Microsoft.Naming", "CA1702:CompoundWordsShouldBeCasedCorrectly", MessageId = "TriState")]
	public class FunctionTriStateGroup : CircuitFunction {
		public FunctionTriStateGroup(CircuitState circuitState, int[] parameter, int result) : base(circuitState, parameter, result) {
		}
		public override bool Evaluate() {
			return this.SetResult0(this.TriStateGroup());
		}

		public override string ReportName { get { return Properties.Resources.TriStateGroupName; } }
	}
}
