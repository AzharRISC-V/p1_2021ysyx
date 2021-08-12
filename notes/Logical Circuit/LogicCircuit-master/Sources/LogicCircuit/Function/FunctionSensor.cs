﻿using System;
using System.Collections.Generic;
using System.Globalization;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Media;

namespace LogicCircuit {
	public class FunctionSensor : CircuitFunction, IFunctionClock, IFunctionVisual {

		public override string ReportName { get { return Properties.Resources.NameSensor; } }

		public bool Invalid { get; set; }

		public CircuitSymbol CircuitSymbol { get; private set; }

		public Sensor Sensor { get { return (Sensor)this.CircuitSymbol.Circuit; } }

		public int BitWidth { get { return this.Sensor.BitWidth; } }

		private readonly SensorValue sensorValue;

		public int Value { get { return this.sensorValue.Value; } }

		private Brush defaultBackground;
		private Brush errorBackground;

		public FunctionSensor(CircuitState circuitState, CircuitSymbol symbol, int[] result) : base(circuitState, null, result) {
			this.CircuitSymbol = symbol;
			Tracer.Assert(this.BitWidth == result.Length);
			switch(this.Sensor.SensorType) {
			case SensorType.Series:
			case SensorType.Loop:
				this.sensorValue = new SeriesValue(this.Sensor.Data, this.Sensor.SensorType == SensorType.Loop, this.Sensor.BitWidth);
				break;
			case SensorType.Random:
				this.sensorValue = new RandomValue(this.Sensor.Data, this.Sensor.BitWidth, this.CircuitState.Random);
				break;
			case SensorType.Manual:
				this.sensorValue = new ManualValue(this.Sensor.Data, this.Sensor.BitWidth);
				break;
			default:
				Tracer.Fail();
				this.sensorValue = null;
				break;
			}
		}

		public bool Flip() {
			return this.sensorValue.Flip();
		}

		public override bool Evaluate() {
			if(this.SetResult(this.Value)) {
				this.Invalid = true;
				return true;
			}
			return false;
		}

		public void TurnOn() {
			if(this.CircuitSymbol.ProbeView is TextBox textBox) {
				textBox.IsEnabled = true;
				textBox.Text = this.Value.ToString("X", CultureInfo.InvariantCulture);
				this.HookupEvents(textBox);
				this.defaultBackground = textBox.Background;
				this.errorBackground = new SolidColorBrush(Color.FromRgb(0xFF, 0x56, 0x16));
			}
		}

		public void TurnOff() {
			if(this.CircuitSymbol.ProbeView is TextBlock textBlock) {
				textBlock.Text = Sensor.UnknownValue;
				return;
			}
			if(this.CircuitSymbol.ProbeView is TextBox textBox) {
				textBox.IsEnabled = false;
				textBox.Text = Sensor.UnknownValue;
				textBox.Background = this.defaultBackground;
				this.UnhookEvents(textBox);
			}
		}

		public void Redraw() {
			if(this.CircuitSymbol.ProbeView is TextBlock textBlock) {
				textBlock.Text = this.Value.ToString("X", CultureInfo.InvariantCulture);
			}
		}

		private void HookupEvents(TextBox textBox) {
			textBox.PreviewKeyUp += textBox_PreviewKeyUp;
			textBox.PreviewLostKeyboardFocus += textBox_PreviewLostKeyboardFocus;
		}

		private void UnhookEvents(TextBox textBox) {
			textBox.PreviewKeyUp -= textBox_PreviewKeyUp;
			textBox.PreviewLostKeyboardFocus += textBox_PreviewLostKeyboardFocus;
		}

		private void textBox_PreviewKeyUp(object sender, KeyEventArgs e) {
			if(sender is TextBox textBox && e.Key == Key.Enter) {
				this.SetManualValue(textBox);
			}
		}

		private void textBox_PreviewLostKeyboardFocus(object sender, KeyboardFocusChangedEventArgs e) {
			if(sender is TextBox textBox) {
				this.SetManualValue(textBox);
			}
		}

		private void SetManualValue(TextBox textBox) {
			if(int.TryParse((textBox.Text ?? string.Empty).Trim(), NumberStyles.HexNumber, CultureInfo.InvariantCulture, out int value)) {
				this.sensorValue.Value = value;
				textBox.Background = this.defaultBackground;
			} else {
				textBox.Background = this.errorBackground;
			}
		}

		private abstract class SensorValue {
			public int BitWidth { get; private set; }

			private int sensorValue;
			public int Value {
				get { return this.sensorValue; }
				set { this.sensorValue = Constant.Normalize(value, this.BitWidth); }
			}

			protected SensorValue(int bitWidth) {
				Tracer.Assert(0 < bitWidth && bitWidth <= 32);
				this.BitWidth = bitWidth;
			}

			public abstract bool Flip();
		}

		private class RandomValue : SensorValue {
			private readonly Random random;
			private readonly int maxValue;
			private readonly int minTick;
			private readonly int maxTick;
			private int flip;
			private int tick;
			
			public RandomValue(string data, int bitWidth, Random random) : base(bitWidth) {
				int minTick;
				int maxTick;
				if(Sensor.TryParsePoint(data, 32, out SensorPoint point)) {
					minTick = point.Tick;
					maxTick = point.Value;
				} else {
					minTick = Sensor.DefaultRandomMinInterval;
					maxTick = Sensor.DefaultRandomMaxInterval;
				}
				Tracer.Assert(0 < minTick && minTick <= maxTick);
				this.random = random;
				this.maxValue = (bitWidth < 32) ? 1 << bitWidth : int.MaxValue;
				this.minTick = minTick;
				this.maxTick = maxTick;
				this.Reset();
				this.Value = this.random.Next(this.maxValue);
			}

			public override bool Flip() {
				if(this.flip == this.tick++) {
					this.Reset();
					this.Value = this.random.Next(this.maxValue);
					return true;
				}
				return false;
			}

			private void Reset() {
				this.flip = this.random.Next(this.minTick, this.maxTick);
				this.tick = 0;
			}
		}

		private class SeriesValue : SensorValue {
			private readonly IList<SensorPoint> list;
			private readonly bool isLoop;
			private int index;
			private int tick;
			private bool stop;

			public SeriesValue(string data, bool isLoop, int bitWidth) : base(bitWidth) {
				if(!Sensor.TryParseSeries(data, bitWidth, out this.list)) {
					this.list = new List<SensorPoint>();
				}
				this.stop = (this.list.Count == 0);
				this.isLoop = isLoop;
				this.Reset();
			}

			public override bool Flip() {
				if(!this.stop && this.list[this.index].Tick == this.tick++) {
					this.Value = this.list[this.index].Value;
					if(this.list.Count <= ++this.index) {
						if(this.isLoop) {
							this.Reset();
						} else {
							this.stop = true;
						}
					}
					return true;
				}
				return false;
			}

			private void Reset() {
				this.index = 0;
				this.tick = 0;
			}
		}

		private class ManualValue : SensorValue {
			private int lastValue;

			public ManualValue(string data, int bitWidth) : base(bitWidth) {
				int value;
				if(string.IsNullOrEmpty(data) || !int.TryParse(data, NumberStyles.HexNumber, CultureInfo.InvariantCulture, out value)) {
					value = 0;
				}
				this.Value = value;
				this.lastValue = value + 1;
			}

			public override bool Flip() {
				if(this.lastValue != this.Value) {
					this.lastValue = this.Value;
					return true;
				}
				return false;
			}
		}
	}
}
