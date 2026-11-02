package analyzers

import "testing"

func TestAll(t *testing.T) {
	for _, a := range All() {
		if a.Name == "" || a.Doc == "" || a.Run == nil {
			t.Errorf("analyzer %q lacks a name, doc, or Run", a.Name)
		}
	}
}
