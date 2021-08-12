﻿using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Input;
using System.Windows.Threading;
using System.Xml;

namespace LogicCircuit {
	public class ScriptConsole : TextBox {
		internal Action<string> CommandEnter { get; set; } = text => {};
		internal Func<bool> CommandBreak { get; set; } = () => false;
		internal Func<string, string> CommandSuggestion { get; set; } = text => string.Empty;

		private int inputStarts;

		private readonly SettingsStringCache historySettings = new SettingsStringCache(Settings.User, "ScriptConsole.History", null);
		private readonly List<string> history;
		private int historyIndex;
		private static int MaxHistoryCount => Settings.User.MaxRecentFileCount * 2;

		public ScriptConsole() {
			this.IsUndoEnabled = false;
			this.AcceptsReturn = true;
			this.AcceptsTab = false;
			this.VerticalScrollBarVisibility = ScrollBarVisibility.Auto;
			this.HorizontalScrollBarVisibility = ScrollBarVisibility.Auto;
			this.CommandBindings.Add(new CommandBinding(
				ApplicationCommands.Paste,
				new ExecutedRoutedEventHandler((sender, e) => {
					this.Paste();
				}),
				new CanExecuteRoutedEventHandler((sender, e) => {
					if(!this.IsEditAllowed()) {
						e.CanExecute = false;
						e.Handled = true;
					}
				})
			));

			this.CommandBindings.Add(new CommandBinding(
				ApplicationCommands.Cut,
				new ExecutedRoutedEventHandler((sender, e) => {
					this.Cut();
				}),
				new CanExecuteRoutedEventHandler((sender, e) => {
					if(!this.IsEditAllowed()) {
						e.CanExecute = false;
						e.Handled = true;
					}
				})
			));

			this.history = this.LoadHistory();
			this.historyIndex = this.history.Count;
		}

		private List<string> LoadHistory() {
			List<string> list = new List<string>();
			string text = this.historySettings.Value;
			if(!string.IsNullOrWhiteSpace(text)) {
				try {
					XmlDocument xml = XmlHelper.LoadXml(text);
					foreach(XmlNode item in xml.SelectNodes("/List/Item")) {
						list.Add(item.InnerText);
					}
				} catch(Exception exception) {
					Tracer.Report("ScriptConsole.LoadHistory", exception);
					//Ignore the exception
				}
				int count = list.Count - ScriptConsole.MaxHistoryCount;
				if(0 < count) {
					list.RemoveRange(0, count);
				}
			}
			return list;
		}

		private void SaveHistory() {
			XmlDocument xml = XmlHelper.Create();
			XmlNode list = xml.AppendChild(xml.CreateElement("List"));
			foreach(string line in this.history) {
				XmlNode item = list.AppendChild(xml.CreateElement("Item"));
				item.InnerText = line;
			}
			this.historySettings.Value = xml.InnerXml;
		}

		private void HistoryAdd(string text) {
			if(!string.IsNullOrWhiteSpace(text)) {
				this.history.Remove(text);
				this.history.Add(text);
				int count = this.history.Count - ScriptConsole.MaxHistoryCount;
				if(0 < count) {
					this.history.RemoveRange(0, count);
				}
				this.historyIndex = this.history.Count;
			}
		}

		private void SetCommand(string text) {
			this.Text = this.Text.Substring(0, this.inputStarts) + text;
			this.Select(this.inputStarts, text.Length);
		}

		private void HistoryUp() {
			if(1 < this.historyIndex) {
				this.SetCommand(this.history[--this.historyIndex]);
			} else if(1 == this.historyIndex) {
				this.SetCommand(this.history[0]);
			}
		}

		private void HistoryDown() {
			int count = this.history.Count - 1;
			if(this.historyIndex < count) {
				this.SetCommand(this.history[this.historyIndex++]);
			} else if(this.historyIndex == count) {
				this.SetCommand(this.history[count]);
			}
		}

		protected override void OnPropertyChanged(DependencyPropertyChangedEventArgs e) {
			base.OnPropertyChanged(e);
			if(e.Property == TextBox.IsUndoEnabledProperty && this.IsUndoEnabled ||
				e.Property == TextBox.AcceptsReturnProperty && !this.AcceptsReturn ||
				e.Property == TextBox.AcceptsTabProperty && this.AcceptsTab
			) {
				throw new InvalidOperationException();
			}
		}

		internal void Prompt(bool fromNewLine, string promptText) {
			if(fromNewLine) {
				string text = this.Text;
				if(0 < text.Length && text[text.Length - 1] != '\n') {
					this.AppendText("\n");
				}
			}
			this.AppendText(promptText);
			this.ScrollToEnd();
			this.inputStarts = this.Text.Length;
			this.Select(this.Text.Length, 0);
		}

		private bool IsEditAllowed() {
			return this.inputStarts <= this.SelectionStart;
		}

		protected override void OnPreviewTextInput(TextCompositionEventArgs e) {
			if(!this.IsEditAllowed()) {
				e.Handled = true;
			} else {
				base.OnPreviewTextInput(e);
			}
		}

		//Left/Right Arrow keys:  Move cursor left or right within text
		//Up/Down Arrow keys:  Move cursor to previous/next line, maintaining position within line
		//Ctrl+Left/Right Arrow:  Move to beginning of previous/next word
		//Ctrl+Up Arrow:  Move to start of text
		//Ctrl+Down Arrow:  Move to end of text
		//Shift+Left/Right/Up/Down Arrow:  Move cursor while selecting text
		//Home key:  Move to beginning of current line
		//End key:  Move to end of current line
		//Shift+Home/End:  Select text to beginning/end of current line
		//Page Up/Down:  Move up/down full page
		//Insert key:  Toggle Insert/Overwrite mode
		//Delete key:  Delete character to right of cursor
		//Backspace key:  Delete character to right of cursor
		//Ctrl+A:  Select all text
		//Ctrl+X:  Cut selected text
		//Ctrl+C:  Copy selected text
		//Ctrl+V:  Paste text at current position
		[SuppressMessage("Microsoft.Maintainability", "CA1502:AvoidExcessiveComplexity")]
		protected override void OnPreviewKeyDown(KeyEventArgs e) {
			try {
				string text;
				switch(e.Key) {
				case Key.Enter:
					text = this.Text.Substring(this.inputStarts);
					this.inputStarts = int.MaxValue;
					base.OnPreviewKeyDown(e);
					this.HistoryAdd(text);
					this.SaveHistory();
					this.AppendText("\n");
					this.Select(this.Text.Length, 0);
					this.ScrollToEnd();
					this.Dispatcher.BeginInvoke(DispatcherPriority.ApplicationIdle, new Action(() => this.CommandEnter(text)));
					e.Handled = true;
					break;
				case Key.Escape:
					if(this.IsEditAllowed()) {
						this.SetCommand(string.Empty);
						e.Handled = true;
					}
					break;
				case Key.Tab:
					if(e.KeyboardDevice.Modifiers == ModifierKeys.None) {
						if(this.IsEditAllowed() && this.Text.Length == this.SelectionStart + this.SelectionLength) {
							text = this.Text.Substring(this.inputStarts, this.SelectionStart - this.inputStarts);
							string suggestion = this.CommandSuggestion(text);
							this.SelectedText = suggestion;
							this.ScrollToEnd();
						}
					} else if(e.KeyboardDevice.Modifiers == ModifierKeys.Control) {
						int start = this.SelectionStart;
						int count = 4 - (start - this.inputStarts) % 4;
						this.SelectedText = new string(' ', count);
						this.Select(start + count, 0);
						this.ScrollToEnd();
					}
					e.Handled = true;
					break;
				case Key.C:
					if(e.KeyboardDevice.Modifiers == ModifierKeys.Control && 0 == this.SelectionLength && this.CommandBreak()) {
						e.Handled = true;
					}
					break;
				case Key.Up:
					if(this.IsEditAllowed()) {
						this.HistoryUp();
						e.Handled = true;
					}
					break;
				case Key.Down:
					if(this.IsEditAllowed()) {
						this.HistoryDown();
						e.Handled = true;
					}
					break;
				case Key.Left:
					if(this.inputStarts == this.SelectionStart && this.SelectionLength == 0 ||
						this.inputStarts < this.SelectionStart &&
						(e.KeyboardDevice.Modifiers & ModifierKeys.Control) == ModifierKeys.Control &&
						string.IsNullOrWhiteSpace(this.Text.Substring(this.inputStarts, this.SelectionStart - this.inputStarts))
					) {
						e.Handled = true;
					}
					break;
				case Key.Home:
					if(this.IsEditAllowed()) {
						if(e.KeyboardDevice.Modifiers == ModifierKeys.Shift) {
							this.Select(this.inputStarts, this.SelectionStart - this.inputStarts);
						} else {
							this.Select(this.inputStarts, 0);
						}
						e.Handled = true;
					}
					break;
				case Key.Delete:
					if(!this.IsEditAllowed()) {
						e.Handled = true;
					}
					break;
				case Key.Back:
					if(this.SelectionStart < this.inputStarts || this.SelectionStart == this.inputStarts && this.SelectionLength == 0) {
						e.Handled = true;
					}
					break;
				default:
					break;
				}
				if(!e.Handled) {
					base.OnPreviewKeyDown(e);
				}
			} catch(Exception exception) {
				App.Mainframe.ReportException(exception);
			}
		}
	}
}
