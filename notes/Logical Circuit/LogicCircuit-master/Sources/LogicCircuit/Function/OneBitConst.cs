﻿using System;

namespace LogicCircuit {
	public class OneBitConst : CircuitFunction {
		private State state;
		public State State { get { return this.state; } }
		public void SetState(State newState) {
			if(this.state != newState) {
				this.state = newState;
				this.CircuitState.MarkUpdated(this);
			}
		}

		public OneBitConst(CircuitState circuitState, State state, int result) : base(circuitState, null, new int[] { result }) {
			this.state = state;
		}
		public override bool Evaluate() {
			return this.SetResult0(this.state);
		}

		public override string ReportName { get { throw new InvalidOperationException(); } }
	}
}
