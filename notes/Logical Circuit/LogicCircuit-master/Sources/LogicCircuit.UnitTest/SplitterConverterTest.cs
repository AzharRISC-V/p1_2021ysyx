﻿using System;
using System.Xml;
using Microsoft.VisualStudio.TestTools.UnitTesting;

namespace LogicCircuit.UnitTest {
	/// <summary>
	/// This is a test class for testing of conversion from version 1.0.0.3
	///</summary>
	[TestClass()]
	public class SplitterConverterTest {
		/// <summary>
		///Gets or sets the test context which provides
		///information about and functionality for the current test run.
		///</summary>
		public TestContext TestContext { get; set; }

		/// <summary>
		/// A test of Clock function
		/// </summary>
		[TestMethod()]
		public void SplitterConvertionTest() {
			string projectText = Properties.Resources.SplitterConversion;
			this.AssertFileVersion(projectText);
			this.AssertConversion(projectText, "Test1");
			this.AssertConversion(projectText, "Test2");
			this.AssertConversion(projectText, "Test3");
			this.AssertConversion(projectText, "Test4");
		}

		private void AssertConversion(string projectText, string initialCircuit) {
			TestSocket test = new TestSocket(new ProjectTester(this.TestContext, projectText, initialCircuit));
			test.Tester.CircuitProject.InTransaction(() => {
				for(int i = 0; i < test.Tester.Input.Length; i++) {
					int bitWidth = test.Tester.Input[i].BitWidth;
					for(int value = 0; value < (1 << bitWidth); value++) {
						test.Tester.Input[i].Value = value;
						Assert.AreEqual(value, test.Tester.Input[i].Value, "Value set incorrectly");
						Assert.IsTrue(test.Tester.CircuitState.Evaluate(true), "Evaluation should be successful");
						Assert.AreEqual(value, test.Value(i, bitWidth), "Incorrect result");
					}
					test.Tester.Input[i].Value = 1 << bitWidth;
					Assert.AreEqual(0, test.Tester.Input[i].Value, "Input should accept values < 1 << bitWidth");
				}
			});
		}

		private void AssertFileVersion(string projectText) {
			XmlDocument xml = new XmlDocument();
			xml.LoadXml(projectText);
			Assert.AreEqual("http://LogicCircuit.net/1.0.0.3/CircuitProject.xsd", xml.DocumentElement.NamespaceURI, "Incorrect file version. File should be of 1.0.0.3 version for this test");
		}

		private class TestSocket {
			public ProjectTester Tester { get; private set; }

			public TestSocket(ProjectTester tester) {
				this.Tester = tester;
				Assert.IsTrue(this.Tester.Input.Length == this.Tester.Output.Length);
			}

			public int Value(int outputIndex, int bitWidth) {
				FunctionProbe probe = this.Tester.Output[outputIndex];
				Assert.AreEqual(bitWidth, probe.BitWidth);
				int result = 0;
				for(int i = 0; i < bitWidth; i++) {
					switch(probe[i]) {
					case State.On0:
						break;
					case State.On1:
						result |= 1 << i;
						break;
					default:
						Assert.Fail("incorrect value");
						break;
					}
				}
				return result;
			}
		}
	}
}
