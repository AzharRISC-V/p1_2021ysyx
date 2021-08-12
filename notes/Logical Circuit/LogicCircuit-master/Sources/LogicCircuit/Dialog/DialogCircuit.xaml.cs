﻿using System;
using System.Collections.Generic;
using System.Linq;
using System.Windows;
using System.Windows.Controls;

namespace LogicCircuit {
	/// <summary>
	/// Interaction logic for DialogCircuit.xaml
	/// </summary>
	public partial class DialogCircuit : Window {

		private SettingsWindowLocationCache windowLocation;
		public SettingsWindowLocationCache WindowLocation { get { return this.windowLocation ?? (this.windowLocation = new SettingsWindowLocationCache(Settings.User, this)); } }
		private readonly LogicalCircuit logicalCircuit;

		public DialogCircuit(LogicalCircuit logicalCircuit) {
			this.DataContext = this;
			this.InitializeComponent();
			this.logicalCircuit = logicalCircuit;
			this.name.Text = this.logicalCircuit.Name;
			this.notation.Text = this.logicalCircuit.Notation;

			HashSet<string> set = new HashSet<string>(this.logicalCircuit.CircuitProject.LogicalCircuitSet.Select(c => c.Category)) {
				string.Empty
			};
			foreach(string s in set.OrderBy(s => s)) {
				this.category.Items.Add(s);
			}

			this.category.Text = this.logicalCircuit.Category;
			if(this.logicalCircuit.ContainsDisplays()) {
				this.isDisplay.IsChecked = this.logicalCircuit.IsDisplay;
			} else {
				this.isDisplay.IsEnabled = false;
			}
			this.description.Text = this.logicalCircuit.Note;

			IEnumerable<Pin> pins(PinSide pinSide) => this.logicalCircuit.Pins.Where(pin => pin.PinSide == pinSide).Select(pin => (Pin)pin);
			this.leftPins.SetPins(pins(PinSide.Left));
			this.rightPins.SetPins(pins(PinSide.Right));
			this.topPins.SetPins(pins(PinSide.Top));
			this.bottomPins.SetPins(pins(PinSide.Bottom));

			bool isFixed = this.IsOrderFixed();
			if(isFixed) {
				this.leftPins.FixOrder();
				this.rightPins.FixOrder();
				this.topPins.FixOrder();
				this.bottomPins.FixOrder();
			}

			this.checkBoxGraphOrder.IsChecked = !isFixed;

			this.Loaded += new RoutedEventHandler(this.DialogCircuitLoaded);
		}

		private void DialogCircuitLoaded(object sender, RoutedEventArgs e) {
			ControlTemplate template = this.category.Template;
			if(template != null) {
				if(template.FindName("PART_EditableTextBox", this.category) is TextBox textBox) {
					SpellCheck spellCheck = textBox.SpellCheck;
					if(spellCheck != null) {
						spellCheck.IsEnabled = true;
					}
				}
			}
		}

		private void CheckBoxGraphOrderClick(object sender, RoutedEventArgs e) {
			try {
				if(!this.checkBoxGraphOrder.IsChecked.Value) {
					this.leftPins.FixOrder();
					this.rightPins.FixOrder();
					this.topPins.FixOrder();
					this.bottomPins.FixOrder();
				} else {
					this.leftPins.Reset();
					this.rightPins.Reset();
					this.topPins.Reset();
					this.bottomPins.Reset();
				}
			} catch(Exception exception) {
				App.Mainframe.ReportException(exception);
			}
		}

		private bool IsOrderFixed() => this.leftPins.IsOrderFixed() || this.rightPins.IsOrderFixed() || this.topPins.IsOrderFixed() || this.bottomPins.IsOrderFixed();

		private void ButtonOkClick(object sender, RoutedEventArgs e) {
			try {
				string name = this.name.Text.Trim();
				string notation = this.notation.Text.Trim();
				string category = this.category.Text.Trim();
				category = category.Substring(0, Math.Min(category.Length, 64)).Trim();
				bool isDisplay = this.logicalCircuit.ContainsDisplays() ? this.isDisplay.IsChecked.Value : this.logicalCircuit.IsDisplay;
				string description = this.description.Text.Trim();
				bool leftChanged = this.leftPins.HasChanges();
				bool rightChanged = this.rightPins.HasChanges();
				bool topChanged = this.topPins.HasChanges();
				bool bottomChanged = this.bottomPins.HasChanges();

				if(this.logicalCircuit.Name != name || this.logicalCircuit.Notation != notation ||
					this.logicalCircuit.Category != category || this.logicalCircuit.IsDisplay != isDisplay || this.logicalCircuit.Note != description ||
					leftChanged || rightChanged || topChanged || bottomChanged
				) {
					this.logicalCircuit.CircuitProject.InTransaction(() => {
						this.logicalCircuit.Rename(name);
						this.logicalCircuit.Notation = notation;
						this.logicalCircuit.Category = category;
						this.logicalCircuit.IsDisplay = isDisplay;
						this.logicalCircuit.Note = description;
						this.logicalCircuit.CircuitProject.CollapsedCategorySet.Purge();
						if(leftChanged) this.leftPins.Update();
						if(rightChanged) this.rightPins.Update();
						if(topChanged) this.topPins.Update();
						if(bottomChanged) this.bottomPins.Update();
					});
				}
				this.Close();
			} catch(Exception exception) {
				App.Mainframe.ReportException(exception);
			}
		}
	}
}
