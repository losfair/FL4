"""Append FL4 extension interfaces after the architecture's existing invocation IDs."""
import sys
import xml.etree.ElementTree as ET

arch, extensions, output = sys.argv[1:]
api = ET.parse(arch)
api.getroot().extend(ET.parse(extensions).getroot())
api.write(output, encoding="utf-8", xml_declaration=True)
