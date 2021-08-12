﻿using System;
using System.Collections.Generic;
using System.Diagnostics.CodeAnalysis;
using System.Linq;
using System.Xml;

namespace LogicCircuit {
	public partial class CollapsedCategory {
	}

	[SuppressMessage("Microsoft.Naming", "CA1710:IdentifiersShouldHaveCorrectSuffix")]
	public sealed partial class CollapsedCategorySet {
		public bool IsCollapsed(string name) {
			return this.Find(name) != null;
		}

		public void SetCollapsed(string name, bool value) {
			CollapsedCategory collapsed = this.Find(name);
			if(value && collapsed == null) {
				this.CircuitProject.InOmitTransaction(() => this.CreateItem(name));
			} else if(!value && collapsed != null) {
				this.CircuitProject.InOmitTransaction(() => collapsed.Delete());
			}
		}

		public void Purge() {
			HashSet<string> category = new HashSet<string>(this.CircuitProject.LogicalCircuitSet.Select(c => c.Category));
			List<CollapsedCategory> list = this.Where(c => !category.Contains(c.Name)).ToList();
			foreach(CollapsedCategory collapsed in list) {
				collapsed.Delete();
			}
		}

		public IRecordLoader CreateRecordLoader(XmlNameTable nameTable) {
			return new RecordLoader<CollapsedCategoryData>(nameTable, this.Table, rowId => this.Create(rowId));
		}
	}
}
