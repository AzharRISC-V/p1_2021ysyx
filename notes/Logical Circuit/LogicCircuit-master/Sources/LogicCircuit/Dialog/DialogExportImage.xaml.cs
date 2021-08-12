﻿using System;
using System.Collections.Generic;
using System.ComponentModel;
using System.Diagnostics.CodeAnalysis;
using System.Globalization;
using System.IO;
using System.Windows;
using System.Windows.Controls;
using System.Windows.Data;
using System.Windows.Media.Imaging;
using Microsoft.Win32;

namespace LogicCircuit {
	/// <summary>
	/// Interaction logic for DialogExportImage.xaml
	/// </summary>
	public partial class DialogExportImage : Window, INotifyPropertyChanged {

		[SuppressMessage("Microsoft.Design", "CA1034:NestedTypesShouldNotBeVisible")]
		public class ImageEncoder {
			public string Name { get; private set; }
			private readonly Func<BitmapEncoder> bitmapEncoder;
			public BitmapEncoder BitmapEncoder { get { return this.bitmapEncoder(); } }

			private readonly string[] extensions;

			public ImageEncoder(string name, Func<BitmapEncoder> bitmapEncoder, params string[] extensions) {
				this.Name = name;
				this.bitmapEncoder = bitmapEncoder;
				this.extensions = extensions;
			}

			public ImageEncoder(string name, Func<BitmapEncoder> bitmapEncoder) : this(name, bitmapEncoder, name) {
			}

			public bool IsKnownExtension(string extension) {
				if(StringComparer.OrdinalIgnoreCase.Compare(this.Name, extension) == 0) {
					return true;
				}
				foreach(string e in this.extensions) {
					if(StringComparer.OrdinalIgnoreCase.Compare(e, extension) == 0) {
						return true;
					}
				}
				return false;
			}

			// This is used in dialog to display encoding names. Do not make it debug only
			public override string ToString() {
				return this.Name;
			}
		}

		public event PropertyChangedEventHandler PropertyChanged;

		private readonly SettingsStringCache imageExportType = new SettingsStringCache(Settings.User, "ImageExport.Type", "Png");
		private readonly SettingsStringCache imageExportFolder = new SettingsStringCache(Settings.User, "ImageExport.Folder", Mainframe.DefaultPictureFolder());

		private readonly Editor editor;

		public IList<ImageEncoder> Encoders { get; private set; }
		public ImageEncoder Encoder { get; set; }
		public string FilePath { get; set; }

		public DialogExportImage(Editor editor) {
			this.editor = editor;
			List<ImageEncoder> list = new List<ImageEncoder> {
				new ImageEncoder("Bmp", () => new BmpBitmapEncoder(), "dib"),
				new ImageEncoder("Gif", () => new GifBitmapEncoder()),
				new ImageEncoder("Jpeg", () => new JpegBitmapEncoder(), "jpg", "jpe"),
				new ImageEncoder("Png", () => new PngBitmapEncoder()),
				new ImageEncoder("Tiff", () => new TiffBitmapEncoder(), "tif")
			};
			this.Encoders = list;
			this.SetEncoder(this.imageExportType.Value);
			this.FilePath = this.DefaultFileName();
			this.DataContext = this;
			this.InitializeComponent();
		}

		private void NotifyPropertyChanged(string property) {
			this.PropertyChanged?.Invoke(this, new PropertyChangedEventArgs(property));
		}

		private string DefaultFileName() {
			string imagePath = this.imageExportFolder.Value;
			if(!Mainframe.IsDirectoryPathValid(imagePath)) {
				imagePath = Mainframe.DefaultPictureFolder();
			}
			string name = string.Format(CultureInfo.InvariantCulture, "{0}.{1}.{2}",
				this.editor.Project.Name,
				this.editor.Project.LogicalCircuit.Name,
				this.Encoder.Name
			);
			return Path.Combine(imagePath, name);
		}

		private void SetFilePath(string filePath) {
			this.FilePath = filePath;
			this.NotifyPropertyChanged("FilePath");
		}

		private ImageEncoder FindEncoder(string extension) {
			foreach(ImageEncoder e in this.Encoders) {
				if(e.IsKnownExtension(extension)) {
					return e;
				}
			}
			return null;
		}

		private void SetEncoder(string extension) {
			ImageEncoder encoder = this.FindEncoder(extension);
			if(encoder == null) {
				encoder = this.FindEncoder("png");
			}
			Tracer.Assert(encoder != null);
			if(this.Encoder != encoder) {
				this.Encoder = encoder;
				this.NotifyPropertyChanged("Encoder");
			}
		}

		private string CurrentExtension() {
			return Path.GetExtension(this.FilePath).Trim().TrimStart('.');
		}

		[SuppressMessage("Microsoft.Performance", "CA1811:AvoidUncalledPrivateCode", Justification="This methid is used in XAML")]
		private void ImageTypeSelectionChanged(object sender, System.Windows.Controls.SelectionChangedEventArgs e) {
			try {
				if(!this.Encoder.IsKnownExtension(this.CurrentExtension())) {
					string path = Path.ChangeExtension(this.FilePath, this.Encoder.Name);
					if(StringComparer.OrdinalIgnoreCase.Compare(path, this.FilePath) != 0) {
						this.SetFilePath(path);
					}
				}
			} catch(Exception exception) {
				App.Mainframe.ReportException(exception);
			}
		}

		private void ButtonFileClick(object sender, RoutedEventArgs e) {
			try {
				string file = this.FilePath;
				if(!Mainframe.IsFilePathValid(file)) {
					file = this.DefaultFileName();
				}
				SaveFileDialog dialog = new SaveFileDialog {
					InitialDirectory = Path.GetDirectoryName(file),
					FileName = Path.GetFileName(file),
					Filter = Properties.Resources.ImageFileFilter,
					DefaultExt = this.Encoder.Name
				};
				bool? result = dialog.ShowDialog(this);
				if(result.HasValue && result.Value) {
					this.SetFilePath(dialog.FileName);
					this.SetEncoder(this.CurrentExtension());
				}
			} catch(Exception exception) {
				App.Mainframe.ReportException(exception);
			}
		}

		private void ButtonOkClick(object sender, RoutedEventArgs e) {
			try {
				BindingExpression filePathBindingExpression = BindingOperations.GetBindingExpression(this.fileName, TextBox.TextProperty);
				filePathBindingExpression.UpdateSource();
				if(File.Exists(this.FilePath)) {
					if(MessageBoxResult.No == DialogMessage.Show(this, this.Title, Properties.Resources.MessageImageFileExists(this.FilePath),
						null, MessageBoxImage.Warning, MessageBoxButton.YesNo
					)) {
						return;
					}

				}
				if(!Mainframe.IsFilePathValid(this.FilePath)) {
					DialogMessage.Show(this, this.Title,
						Properties.Resources.ImagePathInvalid, null, MessageBoxImage.Error, MessageBoxButton.OK
					);
					return;
				}
				RenderTargetBitmap bitmap = this.editor.ExportImage();
				Tracer.Assert(bitmap != null);
				using(FileStream stream = new FileStream(this.FilePath, FileMode.Create)) {
					BitmapEncoder encoder = this.Encoder.BitmapEncoder;
					encoder.Frames.Clear();
					encoder.Frames.Add(BitmapFrame.Create(bitmap));
					encoder.Save(stream);
				}
				this.imageExportType.Value = this.Encoder.Name;
				this.imageExportFolder.Value = Path.GetDirectoryName(this.FilePath);
				e.Handled = true;
				this.DialogResult = true;
			} catch(Exception exception) {
				App.Mainframe.ReportException(exception);
			}
		}
	}
}
