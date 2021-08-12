﻿using System;
using System.Collections.Generic;
using System.Media;
using System.Text.RegularExpressions;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Documents;
using System.Windows.Media.Imaging;

namespace LogicCircuit {
	/// <summary>
	/// Interaction logic for DialogMessage.xaml
	/// </summary>
	public partial class DialogMessage : Window {

		public static MessageBoxResult Show(
			Window parent, string caption, string message, string details, MessageBoxImage image, MessageBoxButton button
		) {
			DialogMessage dialog = new DialogMessage {
				Caption = caption ?? string.Empty,
				Message = message ?? string.Empty,
				Details = details ?? string.Empty,
				image = image,
				MessageBoxButton = button
			};
			dialog.DataContext = dialog;
			dialog.InitializeComponent();
			dialog.Owner = parent;
			dialog.ShowDialog();
			return dialog.messageBoxResult;
		}

		public string Caption { get; private set; }
		public string Message { get; private set; }
		public string Details { get; private set; }
		private MessageBoxImage image;
		public MessageBoxButton MessageBoxButton { get; private set; }
		private MessageBoxResult messageBoxResult = MessageBoxResult.None;

		private DialogMessage() {
			this.Loaded += new RoutedEventHandler(this.DialogMessageLoaded);
		}

		private void SetMessage(string text) {
			try {
				List<string> list = new List<string>();
				int start = 0;
				Regex hyperlink = new Regex("<Hyperlink.*?</Hyperlink>", RegexOptions.Compiled | RegexOptions.Multiline);
				foreach(Match m in hyperlink.Matches(text)) {
					if(0 < m.Index - start) {
						list.Add(text.Substring(start, m.Index - start));
					}
					list.Add(text.Substring(m.Index, m.Length));
					start = m.Index + m.Length;
				}
				if(start < text.Length) {
					list.Add(text.Substring(start));
				}

				List<Inline> inlines = new List<Inline>();
				Regex parts = new Regex("NavigateUri=\"(?<uri>.*)\">(?<text>.*)</Hyperlink>", RegexOptions.Compiled | RegexOptions.Multiline);
				foreach(string s in list) {
					if(hyperlink.IsMatch(s)) {
						Match m = parts.Match(s);
						string uri = m.Groups["uri"].Value;
						string txt = m.Groups["text"].Value;
						Hyperlink link = new Hyperlink(new Run(txt)) {
							NavigateUri = new Uri(uri)
						};
						this.message.Inlines.Add(link);
					} else {
						this.message.Inlines.Add(new Run(s));
					}
				}
				this.message.Inlines.AddRange(inlines);
				return;
			} catch(Exception exception) {
				Tracer.Report("DialogMessage.SetMessage", exception);
			}
			this.message.Inlines.Clear();
			this.message.Text = text;
		}

		private void DialogMessageLoaded(object sender, RoutedEventArgs e) {
			try {
				this.SetMessage(this.Message);
				SystemSound sound;
				switch(this.image) {
				case MessageBoxImage.Information:
					sound = SystemSounds.Asterisk;
					break;
				case MessageBoxImage.Warning:
					sound = SystemSounds.Exclamation;
					break;
				case MessageBoxImage.Question:
					sound = SystemSounds.Question;
					break;
				case MessageBoxImage.Error:
				default:
					sound = SystemSounds.Hand;
					break;
				}
				sound.Play();

				switch(this.MessageBoxButton) {
				case MessageBoxButton.OK:
				default:
					this.OK.IsDefault = this.OK.IsCancel = true;
					this.Yes.Visibility = this.No.Visibility = this.Cancel.Visibility = Visibility.Collapsed;
					this.OK.Focus();
					break;
				case MessageBoxButton.OKCancel:
					this.OK.IsDefault = this.Cancel.IsCancel = true;
					this.Yes.Visibility = this.No.Visibility = Visibility.Collapsed;
					this.OK.Focus();
					break;
				case MessageBoxButton.YesNo:
					this.Yes.IsDefault = true;
					this.OK.Visibility = this.Cancel.Visibility = Visibility.Collapsed;
					this.Yes.Focus();
					break;
				case MessageBoxButton.YesNoCancel:
					this.Yes.IsDefault = this.Cancel.IsCancel = true;
					this.OK.Visibility = Visibility.Collapsed;
					this.Yes.Focus();
					break;
				}
			} catch {
			}
		}

		public FrameworkElement Image {
			get {
				string icon;
				switch(this.image) {
				case MessageBoxImage.Information:
					icon = "/Icon/Info.xaml";
					break;
				case MessageBoxImage.Warning:
					icon = "/Icon/Warning.xaml";
					break;
				case MessageBoxImage.Question:
					icon = "/Icon/Question.xaml";
					break;
				case MessageBoxImage.Error:
				default:
					icon = "/Icon/Error.xaml";
					break;
				}
				return Symbol.Skin(icon);
			}
		}

		private void ButtonClick(object sender, RoutedEventArgs e) {
			Button button = (Button)sender;
			if(button == this.OK) {
				this.messageBoxResult = MessageBoxResult.OK;
			} else if(button == this.Cancel) {
				this.messageBoxResult = MessageBoxResult.Cancel;
			} else if(button == this.Yes) {
				this.messageBoxResult = MessageBoxResult.Yes;
			} else if(button == this.No) {
				this.messageBoxResult = MessageBoxResult.No;
			} else {
				this.messageBoxResult = MessageBoxResult.None;
			}
			this.Close();
		}
	}
}
