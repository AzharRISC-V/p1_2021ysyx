﻿// ------------------------------------------------------------------------------
// <auto-generated>
//     This code was generated by a tool.
//     Runtime Version: 16.0.0.0
//  
//     Changes to this file may cause incorrect behavior and will be lost if
//     the code is regenerated.
// </auto-generated>
// ------------------------------------------------------------------------------
namespace ItemWrapper.Generator
{
    using System.Collections.Generic;
    using System;
    
    /// <summary>
    /// Class to produce the template output
    /// </summary>
    
    #line 1 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
    [global::System.CodeDom.Compiler.GeneratedCodeAttribute("Microsoft.VisualStudio.TextTemplating", "16.0.0.0")]
    public partial class GeneratorItemWrapper : Transformation
    {
#line hidden
        /// <summary>
        /// Create the template output
        /// </summary>
        public override string TransformText()
        {
            this.Write("\t// Class wrapper for a record.\r\n");
            
            #line 4 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"

	string itemClassModifier = string.Empty;
	string itemCtorModifier = "public";
	string itemCtorParamList = ", RowId " + "rowId" + this.Table.Name;
	string itemCtorBaseCall = string.Empty;
	string inheritFrom = "INotifyPropertyChanged";
	bool generateNotifyPropertyChanged = true;
	switch(this.Table.ItemModifier) {
	case ItemModifier.Abstract:
		itemClassModifier = "abstract ";
		itemCtorModifier = "protected";
		break;
	}
	bool isSubclass = this.Table.IsSubclass();
	if(isSubclass) {
		foreach(Table parent in this.Table.Ancestors(false)) {
			itemCtorParamList += ", RowId " + "rowId" + parent.Name;
			itemCtorBaseCall += ", " + "rowId" + parent.Name;
		}
		itemCtorBaseCall = " : base(store" + itemCtorBaseCall + ")";
		inheritFrom = this.Table.BaseName();
		generateNotifyPropertyChanged = false;
	}
	if(this.Table.ItemBaseClass != null) {
		inheritFrom = this.Table.ItemBaseClass;
		generateNotifyPropertyChanged = false;
	}

            
            #line default
            #line hidden
            this.Write("\t");
            
            #line 32 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(itemClassModifier));
            
            #line default
            #line hidden
            this.Write("partial class ");
            
            #line 32 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write(" : ");
            
            #line 32 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(inheritFrom));
            
            #line default
            #line hidden
            this.Write(" {\r\n\r\n\t\t// RowId of the wrapped record\r\n\t\tinternal RowId ");
            
            #line 35 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId { get; private set; }\r\n");
            
            #line 36 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
if(!isSubclass) {
            
            #line default
            #line hidden
            this.Write("\t\t// Store this wrapper belongs to\r\n\t\tpublic ");
            
            #line 38 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(" ");
            
            #line 38 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(" { get; private set; }\r\n");
            
            #line 39 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            this.Write("\r\n\t\t// Constructor\r\n\t\t");
            
            #line 42 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(itemCtorModifier));
            
            #line default
            #line hidden
            this.Write(" ");
            
            #line 42 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("(");
            
            #line 42 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(" store");
            
            #line 42 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(itemCtorParamList));
            
            #line default
            #line hidden
            this.Write(")");
            
            #line 42 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(itemCtorBaseCall));
            
            #line default
            #line hidden
            this.Write(" {\r\n\t\t\tDebug.Assert(!rowId");
            
            #line 43 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write(".IsEmpty);\r\n");
            
            #line 44 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
if(!isSubclass) {
            
            #line default
            #line hidden
            this.Write("\t\t\tthis.");
            
            #line 45 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(" = store;\r\n");
            
            #line 46 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            this.Write("\t\t\tthis.");
            
            #line 47 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId = rowId");
            
            #line 47 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write(";\r\n");
            
            #line 48 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
if(this.RealmType == RealmType.Universe) {
            
            #line default
            #line hidden
            this.Write("\t\t\t// Link back to record. Assuming that a transaction is started\r\n\t\t\tthis.Table." +
                    "SetField(this.");
            
            #line 50 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId, ");
            
            #line 50 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data.");
            
            #line 50 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Field.Field, this);\r\n");
            
            #line 51 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            this.Write("\t\t\tthis.Initialize");
            
            #line 52 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("();\r\n\t\t}\r\n\r\n\t\tpartial void Initialize");
            
            #line 55 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("();\r\n\r\n\t\t// Gets table storing this item.\r\n\t\tprivate TableSnapshot<");
            
            #line 58 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data> Table { get { return this.");
            
            #line 58 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(".");
            
            #line 58 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Set.Table; } }\r\n\r\n");
            
            #line 60 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
if(!isSubclass) {
            
            #line default
            #line hidden
            this.Write("\t\t// Deletes object\r\n\t\tpublic virtual void Delete() {\r\n\t\t\tthis.Table.Delete(this." +
                    "");
            
            #line 63 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId);\r\n\t\t}\r\n\r\n\t\t// Checks if the item is deleted\r\n\t\tpublic bool IsDeleted() {\r\n" +
                    "\t\t\treturn this.Table.IsDeleted(this.");
            
            #line 68 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId);\r\n\t\t}\r\n");
            
            #line 70 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            this.Write("\r\n\t\t//Properties of ");
            
            #line 72 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("\r\n\r\n");
            
            #line 74 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"

foreach(Column column in this.Table.Columns) {
	string access = column.AccessModifierName() + (column.PropertyOverrides ? " override" : string.Empty);
	Key key = this.Table.ForeignKey(column);
	if(key != null && !this.Table.IsPrimary(column)) {
		Table parent = key.Parent();
		Key primaryKey = parent.PrimaryKey();
		string parentId = (primaryKey.KeyType == KeyType.Auto) ? parent.Name + "RowId" : primaryKey[0].Name;
		string findSuffix = (primaryKey.KeyType == KeyType.Auto || !parent.IsSubclass()) ? string.Empty : "By" + parentId;
		string returnType = parent.Name;
		string cast = "";
		if(!string.IsNullOrEmpty(key.PropertyType)) {
			returnType = key.PropertyType;
			cast = "(" + returnType + ")";
		}

            
            #line default
            #line hidden
            this.Write("\t\t// Gets ");
            
            #line 90 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.ReadOnly ? "" : "or sets "));
            
            #line default
            #line hidden
            this.Write("the value referred by the foreign key on field ");
            
            #line 90 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write("\r\n\t\t");
            
            #line 91 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(access));
            
            #line default
            #line hidden
            this.Write(" ");
            
            #line 91 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(returnType));
            
            #line default
            #line hidden
            this.Write(" ");
            
            #line 91 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.PropertyNamePrefix));
            
            #line default
            #line hidden
            
            #line 91 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(key.RoleName()));
            
            #line default
            #line hidden
            this.Write(" {\r\n\t\t\tget { return ");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(cast));
            
            #line default
            #line hidden
            this.Write("this.");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(".");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(parent.Name));
            
            #line default
            #line hidden
            this.Write("Set.Find");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(findSuffix));
            
            #line default
            #line hidden
            this.Write("(this.Table.GetField(this.");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId, ");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data.");
            
            #line 92 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write("Field.Field)); }\r\n");
            
            #line 93 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
		if(!column.ReadOnly) {
            
            #line default
            #line hidden
            this.Write("\t\t\tset { this.Table.SetField(this.");
            
            #line 94 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId, ");
            
            #line 94 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data.");
            
            #line 94 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write("Field.Field, value.");
            
            #line 94 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(parentId));
            
            #line default
            #line hidden
            this.Write("); }\r\n");
            
            #line 95 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
		}
            
            #line default
            #line hidden
            this.Write("\t\t}\r\n");
            
            #line 97 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"

	} else {

            
            #line default
            #line hidden
            this.Write("\t\t// Gets ");
            
            #line 100 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.ReadOnly ? "" : "or sets "));
            
            #line default
            #line hidden
            this.Write("value of the ");
            
            #line 100 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write(" field.\r\n\t\t");
            
            #line 101 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(access));
            
            #line default
            #line hidden
            this.Write(" ");
            
            #line 101 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Type));
            
            #line default
            #line hidden
            this.Write(" ");
            
            #line 101 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.PropertyNamePrefix));
            
            #line default
            #line hidden
            
            #line 101 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write(" {\r\n\t\t\tget { return this.Table.GetField(this.");
            
            #line 102 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId, ");
            
            #line 102 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data.");
            
            #line 102 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write("Field.Field); }\r\n");
            
            #line 103 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
		if(!column.ReadOnly) {
            
            #line default
            #line hidden
            this.Write("\t\t\tset { this.Table.SetField(this.");
            
            #line 104 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("RowId, ");
            
            #line 104 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data.");
            
            #line 104 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write("Field.Field, value); }\r\n");
            
            #line 105 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
		}
            
            #line default
            #line hidden
            this.Write("\t\t}\r\n");
            
            #line 107 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"

	}

            
            #line default
            #line hidden
            this.Write("\r\n");
            
            #line 111 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            
            #line 112 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
if(generateNotifyPropertyChanged) {
            
            #line default
            #line hidden
            this.Write("\t\tpublic event PropertyChangedEventHandler PropertyChanged;\r\n\r\n\t\tprotected void N" +
                    "otifyPropertyChanged(string name) {\r\n\t\t\tPropertyChangedEventHandler handler = th" +
                    "is.PropertyChanged;\r\n\t\t\tif(handler != null) {\r\n");
            
            #line 118 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
	if(this.UseDispatcher) {
            
            #line default
            #line hidden
            this.Write("\t\t\t\tSystem.Windows.Threading.Dispatcher dispatcher = this.");
            
            #line 119 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Store.Name));
            
            #line default
            #line hidden
            this.Write(".Dispatcher;\r\n\t\t\t\tif(dispatcher != null && dispatcher.Thread != System.Threading." +
                    "Thread.CurrentThread) {\r\n\t\t\t\t\tdispatcher.Invoke(new Action<string>(this.NotifyPr" +
                    "opertyChanged), name);\r\n\t\t\t\t\treturn;\r\n\t\t\t\t}\r\n");
            
            #line 124 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
	}
            
            #line default
            #line hidden
            this.Write("\t\t\t\thandler(this, new PropertyChangedEventArgs(name));\r\n\t\t\t}\r\n\t\t}\r\n\r\n\t\tprotected " +
                    "bool HasListener { get { return this.PropertyChanged != null; } }\r\n");
            
            #line 130 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            this.Write("\r\n\t\tinternal void NotifyChanged(TableChange<");
            
            #line 132 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data> change) {\r\n\t\t\tif(this.HasListener) {\r\n\t\t\t\t");
            
            #line 134 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data oldData, newData;\r\n\t\t\t\tchange.GetOldData(out oldData);\r\n\t\t\t\tchange.GetNewDat" +
                    "a(out newData);\r\n");
            
            #line 137 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"

foreach(Column column in this.Table.Columns) {
	Key key = this.Table.ForeignKey(column);
	string propertyName = column.Name;
	if(key != null && !this.Table.IsPrimary(column)) {
		propertyName = key.RoleName();
	}

            
            #line default
            #line hidden
            this.Write("\t\t\t\tif(");
            
            #line 145 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Data.");
            
            #line 145 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(column.Name));
            
            #line default
            #line hidden
            this.Write("Field.Field.Compare(ref oldData, ref newData) != 0) {\r\n\t\t\t\t\tthis.NotifyPropertyCh" +
                    "anged(\"");
            
            #line 146 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(propertyName));
            
            #line default
            #line hidden
            this.Write("\");\r\n\t\t\t\t}\r\n");
            
            #line 148 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
}
            
            #line default
            #line hidden
            this.Write("\t\t\t}\r\n\t\t\tthis.On");
            
            #line 150 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Changed();\r\n\t\t}\r\n\r\n\t\tpartial void On");
            
            #line 153 "C:\Projects\LogicCircuit\LogicCircuit\master\Sources\Tools\ItemWrapper.Generator\GeneratorItemWrapper.tt"
            this.Write(this.ToStringHelper.ToStringWithCulture(this.Table.Name));
            
            #line default
            #line hidden
            this.Write("Changed();\r\n\t}\r\n");
            return this.GenerationEnvironment.ToString();
        }
    }
    
    #line default
    #line hidden
}
